module Main where

import App.Model (binaryOperators)
import App.Runner
import Data.Text
import Fitch.Proof

-----------------------------------------------------------------------------
main :: IO ()
main = runAppFirstOrder exProof functionSymbols predicateSymbols unaryOperators binaryOperators quantifiers
  where
    functionSymbols = [("f", 2)]
    predicateSymbols = [("P", 1), ("A", 0), ("B", 0)]
    unaryOperators = [("~", "¬")]
    binaryOperators = [("/\\", "∧"), ("\\/", "∨"), ("->", "→")]
    quantifiers = [("forall", "∀")]
    fakeModel = initialModelFirstOrder undefined functionSymbols predicateSymbols unaryOperators binaryOperators quantifiers
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
