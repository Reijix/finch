module Specification.FOL where

import Data.Map qualified as M
import Data.Text (Text)
import Fitch.Proof

operatorsFOL :: [(Text, Text, Int)]
operatorsFOL = [("false", "⊥", 0), ("true", "⊤", 0), ("~", "¬", 1), ("/\\", "∧", 2), ("\\/", "∨", 2), ("->", "→", 2)]

infixPredsFOL :: [(Text, Text)]
infixPredsFOL = [("", "=")]

quantifiersFOL :: [(Text, Text)]
quantifiersFOL = [("forall", "∀")]

rulesFOL :: M.Map Text RuleSpec
rulesFOL =
  M.fromList
    [ ("∧I", RuleSpec [phi, psi] [] (phi ∧ psi))
    , ("∧E1", RuleSpec [phi ∧ psi] [] phi)
    , ("∧E2", RuleSpec [phi ∧ psi] [] psi)
    , ("→I", RuleSpec [] [([phi], psi)] (phi → psi))
    , ("→E", RuleSpec [phi, phi → psi] [] psi)
    , ("¬I", RuleSpec [] [([phi], bot)] (neg phi))
    , ("¬E", RuleSpec [phi, neg phi] [] bot)
    , ("¬¬E", RuleSpec [neg $ neg phi] [] phi)
    , ("R", RuleSpec [phi] [] phi)
    , ("∨I1", RuleSpec [phi] [] (phi ∨ psi))
    , ("∨I2", RuleSpec [psi] [] (phi ∨ psi))
    , ("∨E", RuleSpec [phi ∨ psi] [([phi], chi), ([psi], chi)] chi)
    , ("=I", RuleSpec [] [] (FPredicate "=" [TPlaceholder "E", TPlaceholder "E"]))
    ,
      ( "=E"
      , RuleSpec
          [ FSubst "φ" ("x" ~> TPlaceholder "E")
          , FPredicate "=" [TPlaceholder "E", TPlaceholder "D"]
          ]
          []
          (FSubst "φ" ("x" ~> TPlaceholder "D"))
      )
    , ("∀E", RuleSpec [FQuantifier "∀" "x" phi] [] (FSubst "φ" ("x" ~> TPlaceholder "E")))
    ,
      ( "∀I"
      , RuleSpec
          []
          [([FFreshVar "c"], FSubst "φ" ("x" ~> TVar "c"))]
          (FQuantifier "∀" "x" phi)
      )
    ]
 where
  phi :: FormulaSpec
  phi = FPlaceholder "φ"
  psi :: FormulaSpec
  psi = FPlaceholder "ψ"
  chi :: FormulaSpec
  chi = FPlaceholder "χ"
  top :: FormulaSpec
  top = FOp "⊤" []
  bot :: FormulaSpec
  bot = FOp "⊥" []
  neg :: FormulaSpec -> FormulaSpec
  neg f = FOp "¬" [f]
  (∧) :: FormulaSpec -> FormulaSpec -> FormulaSpec
  f1 ∧ f2 = FOp "∧" [f1, f2]
  (∨) :: FormulaSpec -> FormulaSpec -> FormulaSpec
  f1 ∨ f2 = FOp "∨" [f1, f2]
  (→) :: FormulaSpec -> FormulaSpec -> FormulaSpec
  f1 → f2 = FOp "→" [f1, f2]