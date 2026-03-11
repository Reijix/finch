{- |
Module      : Parser.Proof
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module defines parsers for t'Derivation's and full t'Proof's.
-}
module Parser.Proof where

import Data.List.NonEmpty (some1)
import Data.Text qualified as T
import Fitch.Proof
import Parser.Formula
import Parser.Rule
import Parser.Util
import Text.Megaparsec (
  ErrorItem (..),
  PosState (..),
  SourcePos (..),
  defaultTabWidth,
  eitherP,
  eof,
  errorBundlePretty,
  manyTill,
  match,
  pos1,
  runParserT',
  try,
  unexpected,
  (<?>),
 )
import Text.Megaparsec qualified as Parsec

-----------------------------------------------------------------------------

-- * Line parsers

-- | Parses a t'Formula', capturing the source text and wrapping the result in 'ParsedValid'.
pFormula :: (FormulaParser m) => m Formula
pFormula = matchNoSpaces (lexeme pRawFormula) <&> uncurry ParsedValid

-- | Parses an t'Assumption', capturing the source text and wrapping the result in 'ParsedValid'.
pAssumption :: (FormulaParser m) => m Assumption
pAssumption = mkAssumption <$> (matchNoSpaces (lexeme pRawAssumption) <&> uncurry ParsedValid)

-- | Parses a t'Derivation': a t'Formula' followed by a t'RuleApplication'.
pDerivation :: (FormulaParser m) => m Derivation
pDerivation =
  liftA2
    Derivation
    pFormula
    (matchNoSpaces (lexeme pRule) <&> uncurry ParsedValid)

-----------------------------------------------------------------------------

-- * Proof structure parsers

-- | Combinator that gates a parser behind @n@ leading @|@ symbols.
withIndent :: (Parser m) => Int -> m a -> m a
withIndent 0 p = p
withIndent n p = symbol "|" *> withIndent (n - 1) p

{- | Parses the @---@ separator that divides t'Assumption's from t'Derivation's
in a t'Proof', respecting the current indentation depth.
-}
pFormulaSep :: (Parser m) => Int -> m ()
pFormulaSep ind = void . withIndent ind $ symbol "---"

{- | Parses a t'Proof' at the given indentation depth.

The structure is:

1. Zero or more t'Assumption's, collected up to the @---@ separator.
2. One or more t'Derivation's or nested v'SubProof's.
3. The final element must be a t'Derivation'.
-}
pProof :: (FormulaParser m) => Int -> m Proof
pProof ind =
  do
    fs <- manyTill (withIndent ind (lexeme pAssumption)) (try (pFormulaSep ind))
    proofs <-
      some1 . try $ lexeme (eitherP (try $ withIndent ind pDerivation) (pProof (ind + 1)))

    case last proofs of
      Left d -> pure $ SubProof fs (init proofs) d
      Right p -> unexpected (Label $ fromList "subproof")
    <?> "subproof"

-----------------------------------------------------------------------------

-- * Entry points

{- | Parses a single t'Derivation' line from a t'Text'.
Returns 'Left' with a human-readable error message on failure,
or 'Right' with the parsed t'Derivation' on success.
-}
parseLine ::
  -- | List of operators as (alias, operator, arity).
  [(Text, Text, Int)] ->
  -- | List of infix predicates as (alias, predicate).
  [(Text, Text)] ->
  -- | List of quantifiers as (alias, quantifier).
  [(Text, Text)] ->
  -- | Input t'Text' to parse.
  Text ->
  Either Text Derivation
parseLine operators infixPreds quantifiers input = case evalState
  (runParserT' (pDerivation <* eof) initialParserState)
  initialState of
  (_, Left e) -> Left . toText $ errorBundlePretty e
  (_, Right d) -> Right d
 where
  initialParserState =
    Parsec.State
      { stateInput = input
      , stateOffset = 0
      , statePosState =
          PosState
            { pstateInput = input
            , pstateOffset = 0
            , pstateSourcePos = SourcePos{sourceName = "", sourceLine = pos1, sourceColumn = pos1}
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

{- | Parses a full t'Proof' from a t'Text'.
Returns 'Left' with a human-readable error message on failure,
or 'Right' with the parsed t'Proof' on success.
-}
parseProof ::
  -- | List of operators as (alias, operator, arity).
  [(Text, Text, Int)] ->
  -- | List of infix predicates as (alias, predicate).
  [(Text, Text)] ->
  -- | List of quantifiers as (alias, quantifier).
  [(Text, Text)] ->
  -- | Input t'Text' to parse.
  Text ->
  Either Text Proof
parseProof operators infixPreds quantifiers input =
  case evalState
    (runParserT' (pProof 1 <* eof) initialParserState)
    initialState of
    (_, Left e) -> Left . toText $ errorBundlePretty e
    (_, Right p) -> Right p
 where
  initialParserState =
    Parsec.State
      { stateInput = input
      , stateOffset = 0
      , statePosState =
          PosState
            { pstateInput = input
            , pstateOffset = 0
            , pstateSourcePos = SourcePos{sourceName = "", sourceLine = pos1, sourceColumn = pos1}
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
