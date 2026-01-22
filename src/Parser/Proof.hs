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
  { formulaParserState :: FormulaParserState
  , indent :: Int
  }

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

pFormulaSep :: ProofParser ()
pFormulaSep = withIndent $ void $ symbol "---"

withIndent :: ProofParser a -> ProofParser a
withIndent p = gets indent >>= go p
 where
  go :: ProofParser a -> Int -> ProofParser a
  go p 0 = p
  go p n = symbol "|" *> go p (n - 1)

pSubProof :: ProofParser Proof
pSubProof = do
  fs <- manyTill (withIndent (lexeme pAssumption)) (try pFormulaSep)
  proofs <- some . try $ lexeme pProof

  case unsnoc proofs of
    Nothing -> error "pSubProof: unsnoc found empty list after application of `some` combinator! (SHOULD NOT HAPPEN)"
    Just (ps, ProofLine d) -> return $ SubProof fs ps d
    Just _ -> failure Nothing (S.singleton (Label $ NE.fromList "conclusion"))

pProof :: ProofParser Proof
pProof =
  try (withIndent pProofLine)
    <|> ( do
            ind <- gets indent
            modify (\s -> s{indent = ind + 1})
            result <- observing pSubProof
            modify (\s -> s{indent = ind})
            case result of
              Left err -> parseError err
              Right r -> return r
        )
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
parseProof operators quantifiers input = case evalState (runParserT' (pProof <* eof) initialParserState) initialState of
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
      , indent = 0
      }