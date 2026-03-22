{- |
Module      : Parser.Formula
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module defines parsers for t'RawFormula's, t'Term's and t'RawAssumption's.
-}
module Parser.Formula where

import Control.Monad.Combinators.Expr (makeExprParser)
import Fitch.Proof
import Parser.Util
import Text.Megaparsec (
  MonadParsec (..),
  PosState (..),
  SourcePos (..),
  State (..),
  chunk,
  defaultTabWidth,
  errorBundlePretty,
  mkPos,
  pos1,
  runParserT',
  sepBy,
  (<?>),
 )

------------------------------------------------------------------------------------------

-- * Parser state

-- | State for a t'Formula' parser.
data FormulaParserState = FormulaParserState
  { operators :: [(Text, Text, Int)]
  -- ^ List of operators as (alias, operator, arity).
  , infixPreds :: [(Text, Text)]
  -- ^ List of infix predicates as (alias, predicate).
  , quantifiers :: [(Text, Text)]
  -- ^ List of quantifiers as (alias, quantifier).
  }

{- | Constraint alias combining a t'Parser' with a 'MonadState'
over t'FormulaParserState'.
-}
type FormulaParser m = (MonadParsec Void Text m, MonadState FormulaParserState m)

------------------------------------------------------------------------------------------

-- * Term parsers

{- | Parses a function application: a lowercase name followed by a parenthesised,
comma-separated argument list, e.g. @f(x, y)@.

__Note:__ the parser cannot distinguish between function constants and variables.
This does not matter for this application — constants are treated as variables.
-}
pFun :: (FormulaParser m) => m Term
pFun =
  lexeme
    ( liftA2 Fun pLowerName (parens (pTerm `sepBy` comma))
        <?> "function symbol"
    )

-- | Parses a variable: a single lowercase name.
pVar :: (FormulaParser m) => m Term
pVar = lexeme (Var <$> pLowerName <?> "variable")

-- | Parses a t'Term': tries 'pFun' first, then falls back to 'pVar'.
pTerm :: (FormulaParser m) => m Term
pTerm = try pFun <|> pVar <?> "term"

------------------------------------------------------------------------------------------

-- * Formula parsers

{- | Parses a predicate: an uppercase name followed by an optional parenthesised argument list.
Thus also capturing propositional atoms.
-}
pPredicate :: (FormulaParser m) => m RawFormula
pPredicate =
  lexeme
    ( liftA2 Pred pUpperName (parens (pTerm `sepBy` comma) <|> pure [])
        <?> "predicate symbol"
    )

{- | Parses a quantifier name from the current t'FormulaParserState',
accepting both the actual symbol and the alias.
-}
pQuantifierName :: (FormulaParser m) => m Name
pQuantifierName = do
  symbols <- gets quantifiers
  foldr (\(alias, s) p -> chunk s <|> (chunk alias >> pure s) <|> p) empty symbols

{- | Parses a constant, i.e. a nullary 'Opr' like @⊥@
 from the current t'FormulaParserState'.
-}
pConstant :: (FormulaParser m) => m RawFormula
pConstant = do
  ops <- gets operators
  op <-
    foldr
      (\(alias, o, n) p -> if n == 0 then chunk alias <|> chunk o <|> p else p)
      empty
      ops
  lexeme . pure $ Opr op []

-- | Parses a quantified t'RawFormula' of the form @quantifier variable . formula@.
pQuantifier :: (FormulaParser m) => m RawFormula
pQuantifier =
  lexeme $
    liftA3
      Quantifier
      (lexeme pQuantifierName)
      (lexeme (pLowerName <?> "variable"))
      (lexeme (symbol ".") >> lexeme pRawFormula)

{- | Parses an infix predicate name from the current t'FormulaParserState',
accepting both the actual symbol and the alias.
-}
pInfixPredName :: (FormulaParser m) => m Name
pInfixPredName = do
  tops <- gets infixPreds
  foldr (\(alias, s) p -> chunk s <|> (chunk alias >> pure s) <|> p) empty tops

-- | Parses an infix predicate of the form @term predicate term@, e.g. @x = y@.
pInfixPred :: (FormulaParser m) => m RawFormula
pInfixPred = do
  t1 <- lexeme pTerm
  op <- lexeme pInfixPredName
  t2 <- lexeme pTerm
  pure $ InfixPred op t1 t2

{- | Parses an atomic t'RawFormula': a quantifier, infix predicate,
parenthesised formula, constant, or predicate.
-}
pFormulaAtomic :: (FormulaParser m) => m RawFormula
pFormulaAtomic =
  (pQuantifier <|> try pInfixPred <|> parens pRawFormula <|> pConstant <|> pPredicate)
    <?> "formula"

{- | Parses a full t'RawFormula', using 'makeExprParser'
to handle operator precedence and associativity.
-}
pRawFormula :: (FormulaParser m) => m RawFormula
pRawFormula = do
  ops <- gets operators
  let operatorTable =
        [ concatMap
            ( \(alias, u, arity) ->
                if arity == 1
                  then
                    [ prefix alias (\f -> Opr u [f])
                    , prefix u (\f -> Opr u [f])
                    ]
                  else []
            )
            ops
        , concatMap
            ( \(alias, b, arity) ->
                if arity == 2
                  then
                    [ binary alias (\f1 f2 -> Opr b [f1, f2])
                    , binary b (\f1 f2 -> Opr b [f1, f2])
                    ]
                  else []
            )
            ops
        ]
   in makeExprParser pFormulaAtomic operatorTable <?> "formula"

------------------------------------------------------------------------------------------

-- * Assumption parsers

{- | Parses a fresh-variable marker: a lowercase name enclosed in square brackets,
e.g. @[x]@.
-}
pFreshVariable :: (FormulaParser m) => m RawAssumption
pFreshVariable = lexeme $ FreshVar <$> brackets pLowerName

-- | Parses a t'RawAssumption': either a fresh-variable marker or a plain t'RawFormula'.
pRawAssumption :: (FormulaParser m) => m RawAssumption
pRawAssumption = (pFreshVariable <|> (RawAssumption <$> pRawFormula)) <?> "assumption"

------------------------------------------------------------------------------------------

-- * Entry points

{- | Constructs an initial Megaparsec t'Text.Megaparsec.State' positioned at the
given line number, so that parse errors report the correct source location.
-}
initialParserState ::
  -- | Line number at which parsing begins.
  Int ->
  -- | Input t'Text' to parse.
  Text ->
  Text.Megaparsec.State Text e
initialParserState lineNo input =
  State
    { stateInput = input
    , stateOffset = 0
    , statePosState =
        PosState
          { pstateInput = input
          , pstateOffset = 0
          , pstateSourcePos =
              SourcePos{sourceName = "", sourceLine = mkPos lineNo, sourceColumn = pos1}
          , pstateTabWidth = defaultTabWidth
          , pstateLinePrefix = ""
          }
    , stateParseErrors = []
    }

{- | Parses a t'RawFormula' from a t'Text'.
Returns 'Left' with a human-readable error message on failure,
or 'Right' with the parsed t'RawFormula' on success.
-}
parseFormula ::
  -- | Initial parser state.
  FormulaParserState ->
  -- | Line number.
  Int ->
  -- | Input t'Text' to parse.
  Text ->
  Either Text RawFormula
parseFormula initialState lineNo input =
  case evalState
    (runParserT' (pRawFormula <* eof) (initialParserState lineNo input))
    initialState of
    (_, Left e) -> Left . toText $ errorBundlePretty e
    (_, Right f) -> Right f

{- | Parses a t'RawAssumption' from a t'Text'.
Returns 'Left' with a human-readable error message on failure,
or 'Right' with the parsed t'RawAssumption' on success.
-}
parseAssumption ::
  -- | Initial parser state.
  FormulaParserState ->
  -- | Line number.
  Int ->
  -- | Input t'Text' to parse.
  Text ->
  Either Text RawAssumption
parseAssumption initialState lineNo input =
  case evalState
    (runParserT' (pRawAssumption <* eof) (initialParserState lineNo input))
    initialState of
    (_, Left e) -> Left . toText $ errorBundlePretty e
    (_, Right a) -> Right a
