module Main where

import App.Model (operators)
import App.Runner
import Data.Map qualified as M
import Data.Text
import Fitch.Proof

-----------------------------------------------------------------------------
main :: IO ()
main = runApp exProof operators [] M.empty
 where
  operators = [("false", "⊥", 0), ("true", "⊤", 0), ("~", "¬", 1), ("/\\", "∧", 2), ("\\/", "∨", 2), ("->", "→", 2)]
  fakeModel = initialModel undefined operators [] M.empty
  mkFormula :: Text -> Assumption
  mkFormula = tryParse fakeModel [] [] 0

  mkRuleApplication :: Text -> Wrapper RuleApplication
  mkRuleApplication txt = Unparsed txt ""

  mkDerivation :: Text -> Text -> Derivation
  mkDerivation f r = Derivation (mkFormula f) (mkRuleApplication r)

  mkLine :: Text -> Text -> Proof
  mkLine f r = ProofLine $ mkDerivation f r

  exProof :: Proof
  exProof = SubProof [mkFormula "A", mkFormula "A → B"] [mkLine "B" ""] (mkDerivation "A ∧ B" "")

-----------------------------------------------------------------------------