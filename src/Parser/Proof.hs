module Parser.Proof where

import Control.Monad (liftM2)
import Control.Monad.State (MonadState, State, get, gets, modify, put)
import Data.Functor ((<&>))
import Data.Text (Text)
import Data.Void (Void)
import Fitch.Proof (
  Derivation (..),
  Formula,
  Wrapper (ParsedValid),
 )
import Parser.Formula (FormulaParserState, pFormula)
import Parser.Prelude
import Parser.Rule (pRule)
import Text.Megaparsec (ParsecT, match)

data ProofParserState = ProofParserState
  { formulaParserState :: FormulaParserState
  , lineNo :: Int
  , indent :: Int
  }

type ProofParser = ParsecT Void Text (State ProofParserState)

instance {-# OVERLAPPING #-} (MonadState FormulaParserState) ProofParser where
  get :: ProofParser FormulaParserState
  get = gets formulaParserState
  put :: FormulaParserState -> ProofParser ()
  put fps = modify (\state -> state{formulaParserState = fps})

pDerivation :: ProofParser Derivation
pDerivation =
  liftM2
    Derivation
    (match pFormula <&> uncurry ParsedValid)
    (match pRule <&> uncurry ParsedValid)

parseLine :: [(Text, Text, Int)] -> [(Text, Text)] -> Text -> Either Text Formula
parseLine operators quantifiers input = undefined