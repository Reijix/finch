module Parser.Proof where

import Fitch.Proof (
  Assumption,
  Derivation (..),
  Formula,
  Proof (..),
  Wrapper (ParsedValid),
 )
import Parser.Formula (FormulaParser, FormulaParserState (..), pFormula)
import Parser.Prelude (Parser, lexeme, symbol)
import Parser.Rule (pRule)
import Text.Megaparsec (
  ErrorItem (..),
  PosState (..),
  SourcePos (..),
  defaultTabWidth,
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

pAssumption :: (FormulaParser m) => m Assumption
pAssumption = match (lexeme pFormula) <&> uncurry ParsedValid

pDerivation :: (FormulaParser m) => m Derivation
pDerivation =
  liftA2
    Derivation
    pAssumption
    (match (lexeme pRule) <&> uncurry ParsedValid)

pProofLine :: (FormulaParser m) => m Proof
pProofLine = ProofLine <$> pDerivation

pFormulaSep :: (Parser m) => Int -> m ()
pFormulaSep ind = void . withIndent ind $ symbol "---"

withIndent :: (Parser m) => Int -> m a -> m a
withIndent 0 p = p
withIndent n p = symbol "|" *> withIndent (n - 1) p

pSubProof :: (FormulaParser m) => Int -> m Proof
pSubProof ind = do
  fs <- manyTill (withIndent ind (lexeme pAssumption)) (try (pFormulaSep ind))
  proofs <- some . try $ lexeme (pProof ind)

  case viaNonEmpty (\l -> (init l, last l)) proofs of
    Nothing -> error "pSubProof: unsnoc found empty list after application of `some` combinator! (SHOULD NOT HAPPEN)"
    Just (ps, ProofLine d) -> return $ SubProof fs ps d
    Just _ -> unexpected (Label $ fromList "subproof")

pProof :: (FormulaParser m) => Int -> m Proof
pProof ind =
  try (withIndent ind pProofLine)
    <|> pSubProof (ind + 1)
    <?> "subproof or proofline"

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
parseProof operators infixPreds quantifiers input = case evalState (runParserT' (pProof 0 <* eof) initialParserState) initialState of
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