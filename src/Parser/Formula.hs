module Parser.Formula where

import Control.Monad (liftM2, liftM3)
import Control.Monad.Combinators.Expr (
  makeExprParser,
 )
import Control.Monad.State (MonadState, evalState, gets)
import Data.Text (Text, pack)
import Data.Void (Void)
import Fitch.Proof (Formula (..), Name, Term (..))
import Miso.Router (RoutingError (ParseError))
import Parser.Prelude (
  binary,
  brackets,
  comma,
  lexeme,
  pName,
  parens,
  prefix,
  symbol,
 )
import Text.Megaparsec (
  MonadParsec (eof, try),
  PosState (
    PosState,
    pstateInput,
    pstateLinePrefix,
    pstateOffset,
    pstateSourcePos,
    pstateTabWidth
  ),
  SourcePos (SourcePos, sourceColumn, sourceLine, sourceName),
  State (
    State,
    stateInput,
    stateOffset,
    stateParseErrors,
    statePosState
  ),
  chunk,
  defaultTabWidth,
  empty,
  errorBundlePretty,
  mkPos,
  pos1,
  runParserT',
  sepBy,
  (<?>),
  (<|>),
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
pFun = lexeme (liftM2 Fun pName (parens (pTerm `sepBy` comma)) <?> "function")

pVar :: (FormulaParser m) => m Term
pVar = lexeme (Var <$> pName <?> "variable")

pTerm :: (FormulaParser m) => m Term
pTerm = try pFun <|> pVar <?> "term"

pFreshVariable :: (FormulaParser m) => m Formula
pFreshVariable = lexeme $ FreshVar <$> brackets pName

pPredicate :: (FormulaParser m) => m Formula
pPredicate = lexeme $ liftM2 Predicate pName $ parens (pTerm `sepBy` comma) <|> return []

pPropAtom :: (FormulaParser m) => m Formula
pPropAtom = lexeme $ (`Predicate` []) <$> pName

pQuantifierName :: (FormulaParser m) => m Name
pQuantifierName = do
  symbols <- gets quantifiers
  foldr (\(alias, s) p -> chunk s <|> (chunk alias >> return s) <|> p) empty symbols

pConstant :: (FormulaParser m) => m Formula
pConstant = do
  ops <- gets operators
  op <- foldr (\(alias, o, n) p -> if n == 0 then chunk alias <|> chunk o <|> p else p) empty ops
  lexeme . return $ Op op []

pQuantifier :: (FormulaParser m) => m Formula
pQuantifier = lexeme $ liftM3 Quantifier (lexeme pQuantifierName) (lexeme (pName <?> "variable")) (lexeme (symbol ".") >> lexeme pFormula)

pInfixPredName :: (FormulaParser m) => m Name
pInfixPredName = do
  tops <- gets infixPreds
  foldr (\(alias, s) p -> chunk s <|> (chunk alias >> return s) <|> p) empty tops

pInfixPred :: (FormulaParser m) => m Formula
pInfixPred = do
  t1 <- lexeme pTerm
  op <- lexeme pInfixPredName
  t2 <- lexeme pTerm
  return $ Predicate op [t1, t2]

pFormulaAtomic :: (FormulaParser m) => m Formula
pFormulaAtomic = (pFreshVariable <|> pQuantifier <|> try pInfixPred <|> parens pFormula <|> pConstant <|> pPredicate) <?> "formula"

pFormula :: (FormulaParser m) => m Formula
pFormula = do
  ops <- gets operators
  let operatorTable =
        [ concatMap (\(alias, u, arity) -> if arity == 1 then [prefix alias (\f -> Op u [f]), prefix u (\f -> Op u [f])] else []) ops
        , concatMap (\(alias, b, arity) -> if arity == 2 then [binary alias (\f1 f2 -> Op b [f1, f2]), binary b (\f1 f2 -> Op b [f1, f2])] else []) ops
        ]
   in makeExprParser pFormulaAtomic operatorTable <?> "formula"

parseFormula :: [(Text, Text, Int)] -> [(Text, Text)] -> [(Text, Text)] -> Int -> Text -> Either Text Formula
parseFormula operators infixPreds quantifiers lineNo input = case evalState (runParserT' (pFormula <* eof) initialParserState) initialState of
  (_, Left e) -> Left $ pack $ errorBundlePretty e
  (_, Right f) -> Right f
 where
  initialParserState =
    State
      { stateInput = input
      , stateOffset = 0
      , statePosState =
          PosState
            { pstateInput = input
            , pstateOffset = 0
            , pstateSourcePos = SourcePos{sourceName = "", sourceLine = mkPos lineNo, sourceColumn = pos1}
            , pstateTabWidth = defaultTabWidth
            , pstateLinePrefix = ""
            }
      , stateParseErrors = []
      }
  initialState =
    FormulaParserState
      { operators
      , infixPreds
      , quantifiers
      }
