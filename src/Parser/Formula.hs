module Parser.Formula (parseFormula) where

import Control.Monad (liftM2, liftM3)
import Control.Monad.Combinators.Expr (
  Operator (InfixL, Prefix),
  makeExprParser,
 )
import Control.Monad.State qualified as ST
import Data.Data (Proxy (Proxy))
import Data.Set qualified as E
import Data.Text (Text, pack, unpack)
import Data.Text qualified as T
import Data.Void
import Fitch.Proof
import Miso.Router (RoutingError (ParseError))
import Text.Megaparsec
import Text.Megaparsec.Char (letterChar, space1, string)
import Text.Megaparsec.Char.Lexer qualified as L
import Text.Megaparsec.Unicode qualified as Unicode

data FormulaParserState = FormulaParserState
  { operators :: [(Text, Text, Int)]
  , quantifiers :: [(Text, Text)]
  }

type FormulaParser = ParsecT Void Text (ST.State FormulaParserState)

sc :: FormulaParser ()
sc =
  L.space
    space1 -- discard spaces
    empty -- no line comments
    empty -- no block comments

lexeme :: FormulaParser a -> FormulaParser a
lexeme = L.lexeme sc

symbol :: Text -> FormulaParser Text
symbol = L.symbol sc

pName :: FormulaParser Name
pName = lexeme (pack <$> some letterChar <?> "name")

comma :: FormulaParser Text
comma = symbol ","

-- The parser cant distinguish between function constants and variables.
-- This does not matter for our application.
pTerm :: FormulaParser Term
pTerm = lexeme (liftM2 Fun pName (parens (pTerm `sepBy` comma) <|> return []) <?> "term")

parens :: FormulaParser a -> FormulaParser a
parens = between (symbol "(") (symbol ")")

brackets :: FormulaParser a -> FormulaParser a
brackets = between (symbol "[") (symbol "]")

pFreshVariable :: FormulaParser Formula
pFreshVariable = lexeme $ FreshVar <$> brackets pName

pPredicate :: FormulaParser Formula
pPredicate = lexeme $ liftM2 Predicate pName $ parens (pTerm `sepBy` comma) <|> return []

pPropAtom :: FormulaParser Formula
pPropAtom = lexeme $ (`Predicate` []) <$> pName

pQuantifierName :: FormulaParser Name
pQuantifierName = do
  symbols <- ST.gets quantifiers
  foldr (\(alias, s) p -> chunk s <|> (chunk alias >> return s) <|> p) empty symbols

pConstant :: FormulaParser Formula
pConstant = do
  ops <- ST.gets operators
  op <- foldr (\(alias, o, n) p -> if n == 0 then chunk alias <|> chunk o <|> p else p) empty ops
  lexeme . return $ Op op []

pQuantifier :: FormulaParser Formula
pQuantifier = lexeme $ liftM3 Quantifier (lexeme pQuantifierName) (lexeme (pName <?> "variable")) (lexeme (string ".") >> lexeme pFormula)

pFormulaAtomic :: FormulaParser Formula
pFormulaAtomic = (pFreshVariable <|> pQuantifier <|> parens pFormula <|> pConstant <|> pPredicate) <?> "formula"

binary :: Text -> (a -> a -> a) -> Operator FormulaParser a
binary name f = InfixL (f <$ hidden (symbol name))

prefix :: Text -> (a -> a) -> Operator FormulaParser a
prefix name f = Prefix $ foldr1 (.) <$> some (f <$ hidden (symbol name))

pFormula :: FormulaParser Formula
pFormula = do
  ops <- ST.gets operators
  let operatorTable =
        [ concatMap (\(alias, u, arity) -> if arity == 1 then [prefix alias (\f -> Op u [f]), prefix u (\f -> Op u [f])] else []) ops
        , concatMap (\(alias, b, arity) -> if arity == 2 then [binary alias (\f1 f2 -> Op b [f1, f2]), binary b (\f1 f2 -> Op b [f1, f2])] else []) ops
        ]
   in makeExprParser pFormulaAtomic operatorTable <?> "formula"

parseFormula :: [(Text, Text, Int)] -> [(Text, Text)] -> Int -> Text -> Either Text Formula
parseFormula operators quantifiers lineNo input = case ST.evalState (runParserT' (pFormula <* eof) initialParserState) initialState of
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
      , quantifiers
      }
