module Specification.Prop (
  operatorsProp,
  rulesProp,
  emptyProofProp,
  exampleProofsProp,
  initialModelProp,
) where

import App.Model (Model)
import App.Update (initialModel)
import Fitch.Proof (
  AssumptionSpec (..),
  FormulaSpec (FOpr, FPlaceholder),
  Proof (..),
  RuleSpec (..),
 )
import Parser.Proof

operatorsProp :: [(Text, Text, Int)]
operatorsProp =
  [ ("bot", "⊥", 0)
  , ("top", "⊤", 0)
  , ("~", "¬", 1)
  , ("/\\", "∧", 2)
  , ("\\/", "∨", 2)
  , ("->", "→", 2)
  ]

rulesProp :: Map Text RuleSpec
rulesProp =
  [ ("∧I", RuleSpec [phi, psi] [] (phi ∧ psi))
  , ("∧E1", RuleSpec [phi ∧ psi] [] phi)
  , ("∧E2", RuleSpec [phi ∧ psi] [] psi)
  , ("→I", RuleSpec [] [([AssumptionSpec phi], psi)] (phi ↝ psi))
  , ("→E", RuleSpec [phi, phi ↝ psi] [] psi)
  , ("¬I", RuleSpec [] [([AssumptionSpec phi], bot)] (neg phi))
  , ("¬E", RuleSpec [phi, neg phi] [] bot)
  , ("¬¬E", RuleSpec [neg $ neg phi] [] phi)
  , ("R", RuleSpec [phi] [] phi)
  , ("∨I1", RuleSpec [phi] [] (phi ∨ psi))
  , ("∨I2", RuleSpec [psi] [] (phi ∨ psi))
  ,
    ( "∨E"
    , RuleSpec [phi ∨ psi] [([AssumptionSpec phi], chi), ([AssumptionSpec psi], chi)] chi
    )
  , ("⊤I", RuleSpec [] [] (FOpr "⊤" []))
  , ("⊥E", RuleSpec [FOpr "⊥" []] [] phi)
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

readProof :: Text -> Proof
readProof proofText = case parseProof operatorsProp [] [] proofText of
  Left err -> error $ "Could not parse proof:\n" <> proofText <> "\nError:\n" <> err
  Right p -> p

emptyProofProp :: Proof
emptyProofProp =
  readProof
    """
    |---
    |⊤ (⊤I)
    """

exampleProofsProp :: [(Text, Proof)]
exampleProofsProp =
  [
    ( "∧-Symmetry"
    , readProof
        """
        |A ∧ B
        |---
        |B     (∧E2) 1
        |A     (∧E1) 1
        |B ∧ A (∧I) 2,3
        """
    )
  ,
    ( "→-Weakening"
    , readProof
        """
        |A → B ∧ C
        |---
        ||A
        ||---
        ||B ∧ C (→E) 1,2
        ||B     (∧E1) 3
        |A → B  (→I) 2-4
        """
    )
  ]

initialModelProp :: Maybe Proof -> Model
initialModelProp mp =
  initialModel
    emptyProofProp
    (fromMaybe initialP mp)
    exampleProofsProp
    operatorsProp
    []
    []
    rulesProp
 where
  (_, initialP) : _ = exampleProofsProp
