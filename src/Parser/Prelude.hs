module Parser.Prelude where

import Control.Monad.Combinators.Expr (
  Operator (InfixL, Prefix),
 )
import Data.Char (isLetter, isLowerCase, isUpperCase)
import Text.Megaparsec (
  MonadParsec (hidden, takeWhile1P, takeWhileP),
  between,
  (<?>),
 )
import Text.Megaparsec.Char (letterChar, space1)
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = MonadParsec Void Text

sc :: (MonadParsec Void Text m) => m ()
sc =
  L.space
    space1 -- discard spaces
    empty -- no line comments
    empty -- no block comments

lexeme :: (Parser m) => m a -> m a
lexeme = L.lexeme sc

symbol :: (Parser m) => Text -> m Text
symbol = L.symbol sc

pUpperName :: (Parser m) => m Text
pUpperName =
  do
    start <- takeWhile1P (Just "uppercase") isUpperCase
    end <- takeWhileP (Just "letter") isLetter
    pure (start <> end)

pLowerName :: (Parser m) => m Text
pLowerName =
  do
    start <- takeWhile1P (Just "lowercase") isLowerCase
    end <- takeWhileP (Just "letter") isLetter
    pure (start <> end)

pSymbolicName :: (Parser m) => m Text
pSymbolicName = takeWhile1P (Just "symbolic letter") (`notElem` ("()" :: String)) <?> "name"

comma :: (Parser m) => m Text
comma = symbol ","

minus :: (Parser m) => m Text
minus = symbol "-"

parens :: (Parser m) => m a -> m a
parens = between (symbol "(") (symbol ")")

brackets :: (Parser m) => m a -> m a
brackets = between (symbol "[") (symbol "]")

binary :: (Parser m) => Text -> (a -> a -> a) -> Operator m a
binary name f = InfixL (f <$ hidden (symbol name))

prefix :: (Parser m) => Text -> (a -> a) -> Operator m a
prefix name f = Prefix $ foldr (.) id <$> some (f <$ hidden (symbol name))
