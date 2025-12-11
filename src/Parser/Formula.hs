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
  { unaryOperators :: [(Text, Text)]
  , binaryOperators :: [(Text, Text)]
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

pPredicate :: FormulaParser Formula
pPredicate = lexeme $ liftM2 Predicate pName $ parens (pTerm `sepBy` comma) <|> return []

pPropAtom :: FormulaParser Formula
pPropAtom = lexeme $ (`Predicate` []) <$> pName

pQuantifierName :: FormulaParser Name
pQuantifierName = do
  symbols <- ST.gets quantifiers
  foldr (\(alias, s) p -> chunk s <|> (chunk alias >> return s) <|> p) empty symbols

pQuantifier :: FormulaParser Formula
pQuantifier = lexeme $ liftM3 Quantifier (lexeme pQuantifierName) (lexeme (pName <?> "variable")) (lexeme (string ".") >> lexeme pFormula)

pFormulaAtomic :: FormulaParser Formula
pFormulaAtomic = (pQuantifier <|> parens pFormula <|> pPredicate) <?> "formula"

binary :: Text -> (a -> a -> a) -> Operator FormulaParser a
binary name f = InfixL (f <$ hidden (symbol name))

prefix :: Text -> (a -> a) -> Operator FormulaParser a
prefix name f = Prefix $ foldr1 (.) <$> some (f <$ hidden (symbol name))

pFormula :: FormulaParser Formula
pFormula = do
  unaries <- ST.gets unaryOperators
  binaries <- ST.gets binaryOperators
  let operatorTable =
        [ concatMap (\(alias, u) -> [prefix alias (UnaryOp u), prefix u (UnaryOp u)]) unaries
        , concatMap (\(alias, b) -> [binary alias (BinaryOp b), binary b (BinaryOp b)]) binaries
        ]
   in makeExprParser pFormulaAtomic operatorTable <?> "formula"

parseFormula :: [(Text, Text)] -> [(Text, Text)] -> [(Text, Text)] -> Int -> Text -> Either Text Formula
parseFormula unaryOperators binaryOperators quantifiers lineNo input = case ST.evalState (runParserT' (pFormula <* eof) initialParserState) initialState of
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
      { unaryOperators
      , binaryOperators
      , quantifiers
      }
