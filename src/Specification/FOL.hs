module Specification.FOL where

import Fitch.Proof (
  FormulaSpec (
    FFreshVar,
    FOpr,
    FPlaceholder,
    FPred,
    FQuantifier,
    FSubst
  ),
  RuleSpec (..),
  TermSpec (TPlaceholder, TVar),
  (~>),
 )

operatorsFOL :: [(Text, Text, Int)]
operatorsFOL = [("false", "⊥", 0), ("true", "⊤", 0), ("~", "¬", 1), ("/\\", "∧", 2), ("\\/", "∨", 2), ("->", "→", 2)]

infixPredsFOL :: [(Text, Text)]
infixPredsFOL = [("", "=")]

quantifiersFOL :: [(Text, Text)]
quantifiersFOL = [("forall", "∀"), ("exists", "∃")]

rulesFOL :: Map Text RuleSpec
rulesFOL =
  fromList
    [ ("∧I", RuleSpec [phi, psi] [] (phi ∧ psi))
    , ("∧E1", RuleSpec [phi ∧ psi] [] phi)
    , ("∧E2", RuleSpec [phi ∧ psi] [] psi)
    , ("→I", RuleSpec [] [([phi], psi)] (phi ↝ psi))
    , ("→E", RuleSpec [phi, phi ↝ psi] [] psi)
    , ("¬I", RuleSpec [] [([phi], bot)] (neg phi))
    , ("¬E", RuleSpec [phi, neg phi] [] bot)
    , ("¬¬E", RuleSpec [neg $ neg phi] [] phi)
    , ("R", RuleSpec [phi] [] phi)
    , ("∨I1", RuleSpec [phi] [] (phi ∨ psi))
    , ("∨I2", RuleSpec [psi] [] (phi ∨ psi))
    , ("∨E", RuleSpec [phi ∨ psi] [([phi], chi), ([psi], chi)] chi)
    , ("=I", RuleSpec [] [] (FPred "=" [TPlaceholder "E", TPlaceholder "E"]))
    ,
      ( "=E"
      , RuleSpec
          [ FSubst "φ" ("x" ~> TPlaceholder "E")
          , FPred "=" [TPlaceholder "E", TPlaceholder "D"]
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
  phi = FPlaceholder "φ"
  psi = FPlaceholder "ψ"
  chi = FPlaceholder "χ"
  top = FOpr "⊤" []
  bot = FOpr "⊥" []
  neg f = FOpr "¬" [f]
  f1 ∧ f2 = FOpr "∧" [f1, f2]
  f1 ∨ f2 = FOpr "∨" [f1, f2]
  f1 ↝ f2 = FOpr "→" [f1, f2]