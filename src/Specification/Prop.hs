module Specification.Prop where

import Data.Map qualified as M
import Data.Text (Text)
import Fitch.Proof

operatorsProp :: [(Text, Text, Int)]
operatorsProp = [("false", "⊥", 0), ("true", "⊤", 0), ("~", "¬", 1), ("/\\", "∧", 2), ("\\/", "∨", 2), ("->", "→", 2)]

rulesProp :: M.Map Text RuleSpec
rulesProp =
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
 where
  phi = FPlaceholder "φ"
  psi = FPlaceholder "ψ"
  chi = FPlaceholder "χ"
  top = FOp "⊤" []
  bot = FOp "⊥" []
  neg f = FOp "¬" [f]
  f1 ∧ f2 = FOp "∧" [f1, f2]
  f1 ∨ f2 = FOp "∨" [f1, f2]
  f1 → f2 = FOp "→" [f1, f2]