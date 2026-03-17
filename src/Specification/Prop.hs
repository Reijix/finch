{- |
Module      : Specification.Prop
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module provides the specification of propositional logic, i.e. its
operators, rules and some examples.
-}
module Specification.Prop (
  operatorsProp,
  rulesProp,
  exampleProofsProp,
  initialModelProp,
) where

import App.Model (Logic (Prop), Model, initialModel)
import Fitch.Proof
import Miso.Router (URI)
import Parser.Proof
import Specification.Types

------------------------------------------------------------------------------------------

-- * Operators

{- | Operators of propositional logic.

Each entry is a triple @(alias, operator, arity)@, where @alias@ is
ASCII text the parser also accepts and the operator is usually a unicode symbol.
-}
operatorsProp :: [(Text, Text, Int)]
operatorsProp =
  [ ("bot", "⊥", 0)
  , ("top", "⊤", 0)
  , ("~", "¬", 1)
  , ("/\\", "∧", 2)
  , ("\\/", "∨", 2)
  , ("->", "→", 2)
  ]

------------------------------------------------------------------------------------------

-- * Rules

-- | The standard Fitch-style natural deduction rules for propositional logic.
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

------------------------------------------------------------------------------------------

-- * Parser

{- | Parses a t'Proof' of propositional logic.

__Note:__ Should not be used outside of this module, because it uses 'error'.
-}
readProof :: Text -> Proof
readProof proofText = case parseProof operatorsProp [] [] proofText of
  Left err -> error $ "Could not parse proof:\n" <> proofText <> "\nError:\n" <> err
  Right p -> p

------------------------------------------------------------------------------------------

-- * Examples

-- | A list of example t'Proof's shown in the sidebar, each paired with a display name.
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

------------------------------------------------------------------------------------------

-- * Model

-- | Constructs the initial t'Model' for propositional logic.
initialModelProp ::
  -- | The current t'URI' of the application.
  URI ->
  -- | An optional t'Proof' decoded from the URL; falls back to the first example proof.
  Maybe Proof ->
  -- | Whether the user is on a large screen or not.
  Bool ->
  Model
initialModelProp uri mp =
  initialModel
    ( Derivation
        (ParsedValid "⊤" (Opr "⊤" []))
        ( ParsedValid
            "(⊤I)"
            (RuleApplication "⊤I" [])
        )
    )
    (fromMaybe initialP mp)
    exampleProofsProp
    operatorsProp
    []
    []
    rulesProp
    uri
    Prop
 where
  (_, initialP) : _ = exampleProofsProp
