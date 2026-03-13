{- |
Module      : Parser.Util
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module provides shared utility parsers
used across all other @Parser.*@ modules.
-}
module Parser.Util where

import Control.Monad.Combinators.Expr
import Data.Char (isLetter, isLowerCase, isUpperCase)
import Data.Text qualified as T
import Text.Megaparsec (
  MonadParsec (hidden, takeWhile1P, takeWhileP),
  between,
  match,
  (<?>),
 )
import Text.Megaparsec.Char (space1)
import Text.Megaparsec.Char.Lexer qualified as L

------------------------------------------------------------------------------------------

-- * Types

{- | Constraint alias for a Megaparsec parser over a t'Text' stream with no custom
error type.
-}
type Parser = MonadParsec Void Text

------------------------------------------------------------------------------------------

-- * Lexer

-- | Space consumer that only skips whitespace
sc :: (MonadParsec Void Text m) => m ()
sc =
  L.space
    space1 -- discard spaces
    empty -- no line comments
    empty -- no block comments

-- | Wraps a parser so that it consumes trailing whitespace via 'sc'.
lexeme :: (Parser m) => m a -> m a
lexeme = L.lexeme sc

-- | Parses the exact given t'Text' token and consumes any trailing whitespace.
symbol :: (Parser m) => Text -> m Text
symbol = L.symbol sc

-- | Runs a t'Parser' via 'match' but strips whitespace from the resulting 'Text'.
matchNoSpaces :: (Parser m) => m a -> m (Text, a)
matchNoSpaces p = first T.strip <$> match p

------------------------------------------------------------------------------------------

-- * Name parsers

{- | Parses a name that starts with one or more uppercase letters,
followed by zero or more letters.
Used for predicate symbols.
-}
pUpperName :: (Parser m) => m Text
pUpperName =
  do
    start <- takeWhile1P (Just "uppercase") isUpperCase
    end <- takeWhileP (Just "letter") isLetter
    pure (start <> end)

{- | Parses a name that starts with one or more lowercase letters,
followed by zero or more letters.
Used for function symbols and variables.
-}
pLowerName :: (Parser m) => m Text
pLowerName =
  do
    start <- takeWhile1P (Just "lowercase") isLowerCase
    end <- takeWhileP (Just "letter") isLetter
    pure (start <> end)

{- | Parses a symbolic name, i.e. any non-empty sequence of characters
that are neither @(@ nor @)@.
Used for parsing rule applications.
-}
pSymbolicName :: (Parser m) => m Text
pSymbolicName =
  takeWhile1P (Just "symbolic letter") (`notElem` ("()" :: String))
    <?> "name"

{- | Parses arbitrary characters, excluding the control characters
@\\28@, @\\29@, @\\30@, and @\\31@ that are used as separators in
t'Parser.IncompleteProof'.
-}
pText :: (Parser m) => m Text
pText = takeWhileP (Just "text") (`notElem` ("\28\29\30\31" :: String)) <?> "text"

------------------------------------------------------------------------------------------

-- * Symbol parsers

-- | Parses a comma @,@.
comma :: (Parser m) => m Text
comma = symbol ","

-- | Parses a minus sign @-@.
minus :: (Parser m) => m Text
minus = symbol "-"

-- | Wraps a parser between @(@ and @)@.
parens :: (Parser m) => m a -> m a
parens = between (symbol "(") (symbol ")")

-- | Wraps a parser between @[@ and @]@.
brackets :: (Parser m) => m a -> m a
brackets = between (symbol "[") (symbol "]")

------------------------------------------------------------------------------------------

-- * Operator combinators

-- | Creates a left-associative infix operator for use with 'makeExprParser'.
binary :: (Parser m) => Text -> (a -> a -> a) -> Operator m a
binary name f = InfixL (f <$ hidden (symbol name))

{- | Creates a prefix operator for use with 'makeExprParser'.
Defined specifically so that multiple prefix symbols can get parsed without parentheses.
-}
prefix :: (Parser m) => Text -> (a -> a) -> Operator m a
prefix name f = Prefix $ foldr (.) id <$> some (f <$ hidden (symbol name))
