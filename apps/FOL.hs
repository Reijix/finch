module Main where

import App.Model (binaryOperators)
import App.Runner
import Data.Text
import Fitch.Proof

-----------------------------------------------------------------------------
main :: IO ()
main = runApp exProof unaryOperators binaryOperators quantifiers
 where
  unaryOperators = [("~", "¬")]
  binaryOperators = [("/\\", "∧"), ("\\/", "∨"), ("->", "→")]
  quantifiers = [("forall", "∀")]
  fakeModel = initialModel undefined unaryOperators binaryOperators quantifiers
  mkFormula :: Text -> Assumption
  mkFormula = tryParse fakeModel [] 0

  mkRuleApplication :: Text -> Wrapper RuleApplication
  mkRuleApplication = tryParse fakeModel [] 0

  mkDerivation :: Text -> Text -> Derivation
  mkDerivation f r = Derivation (mkFormula f) (mkRuleApplication r)

  mkLine :: Text -> Text -> Proof
  mkLine f r = ProofLine $ mkDerivation f r

  exProof :: Proof
  exProof =
    SubProof
      [mkFormula "A", mkFormula "A → B"]
      [ mkLine "B" "(→E) 1, 2"
      , SubProof
          [mkFormula "A"]
          []
          (mkDerivation "A ∨ B" "(∨I) 4")
      ]
      (mkDerivation "A ∧ B" "(∧I)")

-----------------------------------------------------------------------------

-- exProof :: Proof
-- exProof = SubProof [Parsed "A" $ Predicate "A" []] [] (Derivation (Parsed "A" $ Predicate "A" []) (Parsed "Re" $ RuleApplication (Rule "Re" [] (Predicate "A" [])) []))

-- SubProof
--   [formula "Formula", formula "Formula"]
--   [ ProofLine (Derivation (formula "Formula") (rule "rule" [])),
--     SubProof [formula "Formula"] [ProofLine (Derivation (formula "Formula") (rule "rule" []))] (Derivation (formula "Formula") (rule "rule" [])),
--     SubProof [formula "Formula"] [ProofLine (Derivation (formula "Formula") (rule "rule" []))] (Derivation (formula "Formula") (rule "rule" []))
--   ]
--   (Derivation (formula "Formula") (rule "rule" []))

-----------------------------------------------------------------------------
