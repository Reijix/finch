module Parser.Formula (parseFormula) where

import Control.Monad (liftM2, liftM3)
import Control.Monad.Combinators.Expr (
  Operator (InfixL, Prefix),
  makeExprParser,
 )
import Control.Monad.State
import Data.Text (Text, pack, unpack)
import Data.Text qualified as T
import Fitch.Proof
import Text.Megaparsec (
  MonadParsec (eof, hidden),
  ParsecT,
  ShowErrorComponent (showErrorComponent),
  between,
  chunk,
  empty,
  errorBundlePretty,
  errorBundlePrettyWith,
  parseErrorPretty,
  runParserT,
  sepBy,
  some,
  (<?>),
  (<|>),
 )
import Text.Megaparsec.Char (letterChar, space1, string)
import Text.Megaparsec.Char.Lexer qualified as L

data FormulaParserState = FormulaParserState
  { unaryOperators :: [(Text, Text)]
  , binaryOperators :: [(Text, Text)]
  , quantifiers :: [(Text, Text)]
  }

-- TODO work on error printing
instance ShowErrorComponent Text where
  showErrorComponent :: Text -> String
  showErrorComponent = unpack

type FormulaParser = ParsecT Text Text (State FormulaParserState)

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
  symbols <- gets quantifiers
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
  unaries <- gets unaryOperators
  binaries <- gets binaryOperators
  let operatorTable =
        [ concatMap (\(alias, u) -> [prefix alias (UnaryOp u), prefix u (UnaryOp u)]) unaries
        , concatMap (\(alias, b) -> [binary alias (BinaryOp b), binary b (BinaryOp b)]) binaries
        ]
   in makeExprParser pFormulaAtomic operatorTable <?> "formula"

parseFormula :: [(Text, Text)] -> [(Text, Text)] -> [(Text, Text)] -> Text -> Either Text Formula
parseFormula unaryOperators binaryOperators quantifiers input = case evalState (runParserT (pFormula <* eof) "" input) initialState of
  Left e -> Left . pack $ errorBundlePretty e
  Right f -> Right f
 where
  initialState =
    FormulaParserState
      { unaryOperators
      , binaryOperators
      , quantifiers
      }
