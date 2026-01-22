module Parser.Proof where

import Control.Monad (liftM2, liftM3, void)
import Control.Monad.State (MonadState, State, evalState, get, gets, modify, put)
import Data.Functor ((<&>))
import Data.List (unsnoc)
import Data.List.NonEmpty qualified as NE
import Data.Set qualified as S
import Data.Text (Text, pack)
import Data.Void (Void)
import Fitch.Proof (
  Assumption,
  Derivation (..),
  Formula,
  Proof (..),
  Wrapper (ParsedValid),
 )
import Parser.Formula (FormulaParser, FormulaParserState (..), pFormula)
import Parser.Prelude
import Parser.Rule (pRule)
import Text.Megaparsec hiding (State)
import Text.Megaparsec qualified as Parsec

data ProofParserState = ProofParserState
  {formulaParserState :: FormulaParserState}

type ProofParser = ParsecT Void Text (State ProofParserState)

instance {-# OVERLAPPING #-} (MonadState FormulaParserState) ProofParser where
  get :: ProofParser FormulaParserState
  get = gets formulaParserState
  put :: FormulaParserState -> ProofParser ()
  put fps = modify (\state -> state{formulaParserState = fps})

pAssumption :: (FormulaParser m) => m Assumption
pAssumption = match (lexeme pFormula) <&> uncurry ParsedValid

pDerivation :: (FormulaParser m) => m Derivation
pDerivation =
  liftM2
    Derivation
    pAssumption
    (match (lexeme pRule) <&> uncurry ParsedValid)

pProofLine :: ProofParser Proof
pProofLine = ProofLine <$> pDerivation

pFormulaSep :: Int -> ProofParser ()
pFormulaSep ind = void . withIndent ind $ symbol "---"

withIndent :: Int -> ProofParser a -> ProofParser a
withIndent 0 p = p
withIndent n p = symbol "|" *> withIndent (n - 1) p

pSubProof :: Int -> ProofParser Proof
pSubProof ind = do
  fs <- manyTill (withIndent ind (lexeme pAssumption)) (try (pFormulaSep ind))
  proofs <- some . try $ lexeme (pProof ind)

  case unsnoc proofs of
    Nothing -> error "pSubProof: unsnoc found empty list after application of `some` combinator! (SHOULD NOT HAPPEN)"
    Just (ps, ProofLine d) -> return $ SubProof fs ps d
    Just _ -> failure Nothing (S.singleton (Label $ NE.fromList "conclusion"))

pProof :: Int -> ProofParser Proof
pProof ind =
  try (withIndent ind pProofLine)
    <|> pSubProof (ind + 1)
    <?> "subproof or proofline"

parseLine :: [(Text, Text, Int)] -> [(Text, Text)] -> Text -> Either Text Derivation
parseLine operators quantifiers input = case evalState (runParserT' (pDerivation <* eof) initialParserState) initialState of
  (_, Left e) -> Left $ pack $ errorBundlePretty e
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
      , quantifiers
      }

parseProof :: [(Text, Text, Int)] -> [(Text, Text)] -> Text -> Either Text Proof
parseProof operators quantifiers input = case evalState (runParserT' (pProof 0 <* eof) initialParserState) initialState of
  (_, Left e) -> Left $ pack $ errorBundlePretty e
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
    ProofParserState
      { formulaParserState =
          FormulaParserState
            { operators
            , quantifiers
            }
      }