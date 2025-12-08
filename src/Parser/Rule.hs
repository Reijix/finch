module Parser.Rule (parseRuleApplication) where

import Control.Monad (liftM2, liftM3)
import Control.Monad.Combinators.Expr (
  Operator (InfixL, Prefix),
  makeExprParser,
 )
import Control.Monad.State
import Data.Char (digitToInt)
import Data.Text (Text, pack, unpack)
import Data.Text qualified as T
import Data.Void
import Fitch.Proof
import Text.Megaparsec (
  MonadParsec (eof, hidden, try),
  Parsec,
  between,
  chunk,
  empty,
  errorBundlePretty,
  errorBundlePrettyWith,
  noneOf,
  parseErrorPretty,
  runParser,
  satisfy,
  sepBy,
  some,
  (<?>),
  (<|>),
 )
import Text.Megaparsec.Char (digitChar, letterChar, printChar, space1, string)
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = Parsec Void Text

sc :: Parser ()
sc =
  L.space
    space1 -- discard spaces
    empty -- no line comments
    empty -- no block comments

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

pName :: Parser Name
pName = lexeme (pack <$> some (noneOf ['(', ')']) <?> "name")

comma :: Parser Text
comma = symbol ","

minus :: Parser Text
minus = symbol "-"

pLine :: Parser Int
pLine = lexeme L.decimal <?> "line number"

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

pReference :: Parser Reference
pReference = proofReference <|> lineReference
 where
  proofReference = liftM2 ProofReference (try $ pLine <* lexeme minus) pLine <?> "line range"
  lineReference = LineReference <$> pLine <?> "line number"

pRule :: Parser RuleApplication
pRule = liftM2 RuleApplication (parens pName) (lexeme pReference `sepBy` comma)

parseRuleApplication :: Text -> Either Text RuleApplication
parseRuleApplication input = case runParser (pRule <* eof) "" input of
  Left e -> Left . pack $ errorBundlePretty e
  Right ra -> Right ra
