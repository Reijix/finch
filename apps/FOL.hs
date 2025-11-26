{-# LANGUAGE CPP #-}

module Main where

import App.Model (binaryOperators)
import App.Runner
import Data.Text
import Fitch.Proof

-----------------------------------------------------------------------------
main :: IO ()
main = runApp exProof unaryOperators binaryOperators
  where
    unaryOperators = [("~", "¬")]
    binaryOperators = [("/\\", "∧"), ("\\/", "∨"), ("->", "→")]
    fakeModel = initialModel undefined unaryOperators binaryOperators
    mkFormula :: Text -> Assumption
    mkFormula = tryParse fakeModel []

    mkRuleApplication :: Text -> ParseWrapper RuleApplication
    mkRuleApplication txt = Unparsed txt ""

    mkDerivation :: Text -> Text -> Derivation
    mkDerivation f r = Derivation (mkFormula f) (mkRuleApplication r)

    mkLine :: Text -> Text -> Proof
    mkLine f r = ProofLine $ mkDerivation f r

    exProof :: Proof
    exProof = SubProof [mkFormula "A", mkFormula "A → B"] [mkLine "B" ""] (mkDerivation "A ∧ B" "")

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
