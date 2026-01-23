module Main where

import App.Model (operators)
import App.Runner
import Data.Map qualified as M
import Data.Text
import Fitch.Proof

-----------------------------------------------------------------------------
main :: IO ()
main = runApp exProof operators infixPreds quantifiers rules
 where
  operators = [("false", "⊥", 0), ("true", "⊤", 0), ("~", "¬", 1), ("/\\", "∧", 2), ("\\/", "∨", 2), ("->", "→", 2)]
  infixPreds = [("", "=")]
  quantifiers = [("forall", "∀")]
  rules =
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

  phi = FPlaceholder "φ"
  psi = FPlaceholder "ψ"
  chi = FPlaceholder "χ"
  top = FOp "⊤" []
  bot = FOp "⊥" []
  neg f = FOp "¬" [f]
  f1 ∧ f2 = FOp "∧" [f1, f2]
  f1 ∨ f2 = FOp "∨" [f1, f2]
  f1 → f2 = FOp "→" [f1, f2]
  fakeModel = initialModel undefined operators infixPreds quantifiers M.empty

  mkFormula :: Text -> Assumption
  mkFormula = tryParse fakeModel [] [] [] 1

  mkRuleApplication :: Text -> Wrapper RuleApplication
  mkRuleApplication = tryParse fakeModel [] [] [] 1

  mkDerivation :: Text -> Text -> Derivation
  mkDerivation f r = Derivation (mkFormula f) (mkRuleApplication r)

  mkLine :: Text -> Text -> Proof
  mkLine f r = ProofLine $ mkDerivation f r

  exProof :: Proof
  exProof =
    SubProof
      [mkFormula "A", mkFormula "A → B"]
      [ mkLine "P(x)" "(→E) 1, 2"
      , mkLine "x = y" "(→E) 1, 2"
      , SubProof
          [mkFormula "[c]"]
          []
          (mkDerivation "c = c" "(∨I1) 4")
      ]
      (mkDerivation "P(y)" "(=E) 3,4")

-----------------------------------------------------------------------------