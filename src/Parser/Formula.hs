module Parser.Formula (parseFormula) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Control.Monad.State
import Data.Text (Text, pack, unpack)
import Fitch.Proof
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

data FormulaParserState = FormulaParserState
  { unaryOperators :: [(Text, Text)],
    binaryOperators :: [(Text, Text)],
    quantifiers :: [(Text, Text)]
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

pFun :: FormulaParser Term
pFun = lexeme $ liftM2 Fun pName $ choice [try $ parens (pTerm `sepBy` comma), return []]

pVar :: FormulaParser Term
pVar = Var <$> lexeme (pack <$> some letterChar <?> "variable")

parens :: FormulaParser a -> FormulaParser a
parens = between (symbol "(") (symbol ")")

pTermAtomic :: FormulaParser Term
pTermAtomic = choice [try pFun, pVar]

pTerm :: FormulaParser Term
pTerm = makeExprParser pTermAtomic []

pPredicate :: FormulaParser Formula
pPredicate = lexeme $ liftM2 Predicate pName $ choice [try $ parens (pTerm `sepBy` comma), return []]

pPropAtom :: FormulaParser Formula
pPropAtom = lexeme $ (`Predicate` []) <$> pName

pQuantifierName :: FormulaParser Name
pQuantifierName = do
  symbols <- gets quantifiers
  foldr (\(alias, s) p -> chunk s <|> (chunk alias >> return s) <|> p) empty symbols

pQuantifier :: FormulaParser Formula
pQuantifier = lexeme $ liftM3 Quantifier (lexeme pQuantifierName) (lexeme pName) (lexeme (string ".") >> lexeme pFormula)

pFormulaAtomic :: FormulaParser Formula
pFormulaAtomic = choice [try pQuantifier, try pPredicate, parens pFormula]

binary :: Text -> (a -> a -> a) -> Operator FormulaParser a
binary name f = InfixL (f <$ symbol name)

prefix, postfix :: Text -> (a -> a) -> Operator FormulaParser a
prefix name f = Prefix (f <$ symbol name)
postfix name f = Postfix (f <$ symbol name)

pFormula :: FormulaParser Formula
pFormula = do
  unaries <- gets unaryOperators
  binaries <- gets binaryOperators
  let operatorTable =
        [ concatMap (\(alias, u) -> [prefix alias (UnaryOp u), prefix u (UnaryOp u)]) unaries,
          concatMap (\(alias, b) -> [binary alias (BinaryOp b), binary b (BinaryOp b)]) binaries
        ]
   in makeExprParser pFormulaAtomic operatorTable

parseFormula :: [(Text, Text)] -> [(Text, Text)] -> [(Text, Text)] -> Text -> Either Text Formula
parseFormula unaryOperators binaryOperators quantifiers input = case evalState (runParserT (pFormula <* eof) "" input) initialState of
  Left e -> Left "error"
  Right f -> Right f
  where
    initialState =
      FormulaParserState
        { unaryOperators,
          binaryOperators,
          quantifiers
        }
