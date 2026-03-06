module Parser.Formula where

import Control.Monad.Combinators.Expr (makeExprParser)
import Fitch.Proof (Name, RawAssumption (..), RawFormula (..), Term (..))
import Parser.Util (
  binary,
  brackets,
  comma,
  lexeme,
  pLowerName,
  pUpperName,
  parens,
  prefix,
  symbol,
 )
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

data FormulaParserState = FormulaParserState
  { operators :: [(Text, Text, Int)]
  , infixPreds :: [(Text, Text)]
  , quantifiers :: [(Text, Text)]
  }

type FormulaParser m = (MonadParsec Void Text m, MonadState FormulaParserState m)

-- The parser cant distinguish between function constants and variables.
-- This does not matter for our application. => constants are treated as variables!
pFun :: (FormulaParser m) => m Term
pFun = lexeme (liftA2 Fun pLowerName (parens (pTerm `sepBy` comma)) <?> "function symbol")

pVar :: (FormulaParser m) => m Term
pVar = lexeme (Var <$> pLowerName <?> "variable")

pTerm :: (FormulaParser m) => m Term
pTerm = try pFun <|> pVar <?> "term"

pFreshVariable :: (FormulaParser m) => m RawAssumption
pFreshVariable = lexeme $ FreshVar <$> brackets pLowerName

pPredicate :: (FormulaParser m) => m RawFormula
pPredicate =
  lexeme
    (liftA2 Pred pUpperName (parens (pTerm `sepBy` comma) <|> pure []) <?> "predicate symbol")

pPropAtom :: (FormulaParser m) => m RawFormula
pPropAtom = lexeme $ (`Pred` []) <$> pUpperName

pQuantifierName :: (FormulaParser m) => m Name
pQuantifierName = do
  symbols <- gets quantifiers
  foldr (\(alias, s) p -> chunk s <|> (chunk alias >> pure s) <|> p) empty symbols

pConstant :: (FormulaParser m) => m RawFormula
pConstant = do
  ops <- gets operators
  op <-
    foldr (\(alias, o, n) p -> if n == 0 then chunk alias <|> chunk o <|> p else p) empty ops
  lexeme . pure $ Opr op []

pQuantifier :: (FormulaParser m) => m RawFormula
pQuantifier =
  lexeme $
    liftA3
      Quantifier
      (lexeme pQuantifierName)
      (lexeme (pLowerName <?> "variable"))
      (lexeme (symbol ".") >> lexeme pRawFormula)

pInfixPredName :: (FormulaParser m) => m Name
pInfixPredName = do
  tops <- gets infixPreds
  foldr (\(alias, s) p -> chunk s <|> (chunk alias >> pure s) <|> p) empty tops

pInfixPred :: (FormulaParser m) => m RawFormula
pInfixPred = do
  t1 <- lexeme pTerm
  op <- lexeme pInfixPredName
  t2 <- lexeme pTerm
  pure $ Pred op [t1, t2]

pFormulaAtomic :: (FormulaParser m) => m RawFormula
pFormulaAtomic =
  (pQuantifier <|> try pInfixPred <|> parens pRawFormula <|> pConstant <|> pPredicate)
    <?> "formula"

pRawFormula :: (FormulaParser m) => m RawFormula
pRawFormula = do
  ops <- gets operators
  let operatorTable =
        [ concatMap
            ( \(alias, u, arity) ->
                if arity == 1 then [prefix alias (\f -> Opr u [f]), prefix u (\f -> Opr u [f])] else []
            )
            ops
        , concatMap
            ( \(alias, b, arity) ->
                if arity == 2
                  then [binary alias (\f1 f2 -> Opr b [f1, f2]), binary b (\f1 f2 -> Opr b [f1, f2])]
                  else []
            )
            ops
        ]
   in makeExprParser pFormulaAtomic operatorTable <?> "formula"

pRawAssumption :: (FormulaParser m) => m RawAssumption
pRawAssumption = (pFreshVariable <|> (RawAssumption <$> pRawFormula)) <?> "assumption"

initialParserState :: Int -> Text -> Text.Megaparsec.State Text e
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

parseFormula :: FormulaParserState -> Int -> Text -> Either Text RawFormula
parseFormula initialState lineNo input =
  case evalState
    (runParserT' (pRawFormula <* eof) (initialParserState lineNo input))
    initialState of
    (_, Left e) -> Left . toText $ errorBundlePretty e
    (_, Right f) -> Right f

parseAssumption :: FormulaParserState -> Int -> Text -> Either Text RawAssumption
parseAssumption initialState lineNo input =
  case evalState
    (runParserT' (pRawAssumption <* eof) (initialParserState lineNo input))
    initialState of
    (_, Left e) -> Left . toText $ errorBundlePretty e
    (_, Right a) -> Right a
