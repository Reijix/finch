module Main where

import App.Model (operators)
import App.Runner
import Data.Map qualified as M
import Data.Text
import Fitch.Proof

-----------------------------------------------------------------------------
main :: IO ()
main = runApp exProof operators [] rules
 where
  operators = [("false", "⊥", 0), ("true", "⊤", 0), ("~", "¬", 1), ("/\\", "∧", 2), ("\\/", "∨", 2), ("->", "→", 2)]
  rules =
    M.fromList
      [ ("∧I", RuleSpec [phi, psi] [] (phi ∧ psi))
      , ("∧E1", RuleSpec [phi ∧ psi] [] phi)
      , ("∧E2", RuleSpec [phi ∧ psi] [] psi)
      , ("→I", RuleSpec [] [([phi], psi)] (phi → psi))
      , ("→E", RuleSpec [phi → psi, phi] [] psi)
      , ("¬I", RuleSpec [] [([phi], bot)] (neg phi))
      , ("¬E", RuleSpec [phi, neg phi] [] bot)
      , ("¬¬E", RuleSpec [neg $ neg phi] [] phi)
      , ("R", RuleSpec [phi] [] phi)
      , ("∨I1", RuleSpec [phi] [] (phi ∨ psi))
      , ("∨I2", RuleSpec [psi] [] (phi ∨ psi))
      , ("∨E", RuleSpec [phi ∨ psi] [([phi], chi), ([psi], chi)] chi)
      ]
  phi = FVar "φ"
  psi = FVar "ψ"
  chi = FVar "χ"
  top = FOp "⊤" []
  bot = FOp "⊥" []
  neg f = FOp "¬" [f]
  f1 ∧ f2 = FOp "∧" [f1, f2]
  f1 ∨ f2 = FOp "∨" [f1, f2]
  f1 → f2 = FOp "→" [f1, f2]

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