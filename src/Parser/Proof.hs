module Parser.Proof where

import Data.List.NonEmpty (some1)
import Fitch.Proof (
  Assumption,
  Derivation (..),
  Formula,
  Proof (..),
  RawAssumption (..),
  RawFormula,
  Wrapper (ParsedValid),
  mkAssumption,
 )
import Parser.Formula (FormulaParser, FormulaParserState (..), pFreshVariable, pRawAssumption, pRawFormula)
import Parser.Prelude (Parser, lexeme, symbol)
import Parser.Rule (pRule)
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

pFormula :: (FormulaParser m) => m Formula
pFormula = match (lexeme pRawFormula) <&> uncurry ParsedValid

pAssumption :: (FormulaParser m) => m Assumption
pAssumption = mkAssumption <$> (match (lexeme pRawAssumption) <&> uncurry ParsedValid)

pDerivation :: (FormulaParser m) => m Derivation
pDerivation =
  liftA2
    Derivation
    pFormula
    (match (lexeme pRule) <&> uncurry ParsedValid)

pFormulaSep :: (Parser m) => Int -> m ()
pFormulaSep ind = void . withIndent ind $ symbol "---"

withIndent :: (Parser m) => Int -> m a -> m a
withIndent 0 p = p
withIndent n p = symbol "|" *> withIndent (n - 1) p

pProof :: (FormulaParser m) => Int -> m Proof
pProof ind =
  do
    fs <- manyTill (withIndent ind (lexeme pAssumption)) (try (pFormulaSep ind))
    proofs <- some1 . try $ lexeme (eitherP (try $ withIndent ind pDerivation) (pProof (ind + 1)))

    case last proofs of
      Left d -> pure $ SubProof fs (init proofs) d
      Right _ -> unexpected (Label $ fromList "subproof")
    <?> "subproof"

parseLine :: [(Text, Text, Int)] -> [(Text, Text)] -> [(Text, Text)] -> Text -> Either Text Derivation
parseLine operators infixPreds quantifiers input = case evalState (runParserT' (pDerivation <* eof) initialParserState) initialState of
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

parseProof :: [(Text, Text, Int)] -> [(Text, Text)] -> [(Text, Text)] -> Text -> Either Text Proof
parseProof operators infixPreds quantifiers input = case evalState (runParserT' (pProof 1 <* eof) initialParserState) initialState of
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