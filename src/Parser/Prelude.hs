module Parser.Prelude where

import Control.Monad.Combinators.Expr (
  Operator (InfixL, Prefix),
 )
import Data.Text (Text, pack)
import Data.Void (Void)
import Text.Megaparsec (
  MonadParsec (hidden),
  between,
  empty,
  noneOf,
  some,
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

pName :: (Parser m) => m Text
pName = pack <$> some letterChar <?> "name"

pSymbolicName :: (Parser m) => m Text
pSymbolicName = pack <$> some (noneOf ['(', ')']) <?> "name"

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
prefix name f = Prefix $ foldr1 (.) <$> some (f <$ hidden (symbol name))
