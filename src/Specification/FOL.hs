{- |
Module      : Specification.FOL
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module provides the specification of first-order logic, i.e. its
operators, rules and some examples. This module extends "Specification.Prop"
-}
module Specification.FOL (
  operatorsFOL,
  infixPredsFOL,
  quantifiersFOL,
  rulesFOL,
  emptyProofFOL,
  exampleProofsFOL,
  initialModelFOL,
) where

import Miso.Router (URI)

import App.Model
import Fitch.Proof
import Parser.Proof (parseProof)
import Specification.Prop
import Specification.Types

-----------------------------------------------------------------------------

-- * Operators

{- | Operators of first-order logic.

Each entry is a triple @(alias, operator, arity)@, where @alias@ is
ASCII text the parser also accepts and the operator is usually a unicode symbol.

Operators are inherited from 'operatorsProp'.
-}
operatorsFOL :: [(Text, Text, Int)]
operatorsFOL = operatorsProp

-----------------------------------------------------------------------------

-- * Infix Predicates

{- | Infix predicates of first-order logic.

Each entry is a pair @(alias, predicate)@, where @alias@ is ASCII text
the parser also accepts.
-}
infixPredsFOL :: [(Text, Text)]
infixPredsFOL = [("", "=")]

-----------------------------------------------------------------------------

-- * Quantifiers

{- | Quantifiers of first-order logic.

Each entry is a pair @(alias, quantifier)@, where @alias@ is ASCII text
the parser also accepts and @quantifier@ is a unicode symbol.
-}
quantifiersFOL :: [(Text, Text)]
quantifiersFOL = [("forall", "∀"), ("exists", "∃")]

-----------------------------------------------------------------------------

-- * Rules

{- | The standard Fitch-style natural deduction rules for first-order logic.

Extends 'rulesProp' with rules for @∀@, @∃@ and @=@.
-}
rulesFOL :: Map Text RuleSpec
rulesFOL =
  rulesProp
    <> [ ("=I", RuleSpec [] [] (FInfixPred "=" (TPlaceholder "E") (TPlaceholder "E")))
       ,
         ( "=E"
         , RuleSpec
             [ FSubst "φ" ("x" ~> "E")
             , FInfixPred "=" (TPlaceholder "E") (TPlaceholder "D")
             ]
             []
             (FSubst "φ" ("x" ~> "D"))
         )
       , ("∀E", RuleSpec [FQuantifier "∀" "x" phi] [] (FSubst "φ" ("x" ~> "E")))
       ,
         ( "∀I"
         , RuleSpec
             []
             [([FFreshVar "c"], FSubst "φ" ("x" ~> "c"))]
             (FQuantifier "∀" "x" phi)
         )
       , ("∃I", RuleSpec [FSubst "φ" ("x" ~> "E")] [] (FQuantifier "∃" "x" phi))
       ,
         ( "∃E"
         , RuleSpec
             [FQuantifier "∃" "x" phi]
             [([FFreshVar "c", AssumptionSpec $ FSubst "φ" ("x" ~> "c")], psi)]
             psi
         )
       ]
 where
  phi = FPlaceholder "φ"
  psi = FPlaceholder "ψ"

-----------------------------------------------------------------------------

-- * Parser

{- | Parses a t'Proof' of first-order logic.

__Note:__ Should not be used outside of this module, because it uses 'error'.
-}
readProof :: Text -> Proof
readProof proofText = case parseProof operatorsFOL infixPredsFOL quantifiersFOL proofText of
  Left err -> error $ "Could not parse proof:\n" <> proofText <> "\nError:\n" <> err
  Right p -> p

-----------------------------------------------------------------------------

-- * Examples

-- | The default empty t'Proof' shown when the user starts a new proof in first-order-logic mode.
emptyProofFOL :: Proof
emptyProofFOL =
  readProof
    """
    |---
    |⊤ (⊤I)
    """

-- | A list of example t'Proof's shown in the sidebar, each paired with a display name.
exampleProofsFOL :: [(Text, Proof)]
exampleProofsFOL =
  [
    ( "∀-Transitivity"
    , readProof
        """
        |∀x. P(x) → Q(x)
        |∀z. Q(z) → R(z)
        |---
        ||[d]
        ||---
        |||P(d)
        |||---
        |||P(d) → Q(d)  (∀E) 1
        |||Q(d)         (→E) 4,5
        |||Q(d) → R(d)  (∀E) 2
        |||R(d)         (→E) 6,7
        ||P(d) → R(d)   (→I) 4-8
        |∀x.P(x) → R(x) (∀I) 3-9
        """
    )
  ,
    ( "=-Symmetry"
    , readProof
        """
        |e = d
        |---
        |e = e (=I)
        |d = e (=E) 2,1
        """
    )
  ,
    ( "∀-to-∃"
    , readProof
        """
        |¬∀x.¬P(x)
        |---
        ||¬∃x.P(x)
        ||---
        |||[c]
        |||---
        ||||P(c)
        ||||---
        ||||∃x.P(x) (∃I) 4
        ||||⊥       (¬E) 5,2
        |||¬P(c)    (¬I) 4-6
        ||∀x.¬P(x)  (∀I) 3-7
        ||⊥         (¬E) 8,1
        |¬¬∃x.P(x)  (¬I) 2-9
        |∃x.P(x)    (¬¬E) 10
        """
    )
  ,
    ( "∃-to-∀"
    , readProof
        """
        |∃x.P(x)
        |---
        ||[c]
        ||P(c)
        ||---
        |||∀x.¬P(x)
        |||---
        |||¬P(c)    (∀E) 4
        |||⊥        (¬E) 3,5
        ||¬∀x.¬P(x) (¬I) 4-6
        |¬∀x.¬P(x)  (∃E) 1, 2-7
        """
    )
  ,
    ( "∃∀-to-∀∃"
    , readProof
        """
        |∃x.∀y.P(x,y)
        |---
        ||[c]
        ||∀y.P(c,y)
        ||---
        |||[d]
        |||---
        |||P(c,d)      (∀E) 3
        |||∃x.P(x,d)   (∃I) 5
        ||∀y.∃x.P(x,y) (∀I) 4-6
        |∀y.∃x.P(x,y)  (∃E) 1, 2-7
        """
    )
  ]

-----------------------------------------------------------------------------

-- * Model

-- | Constructs the initial t'Model' for first-order-logic.
initialModelFOL ::
  -- | The current t'URI' of the application.
  URI ->
  -- | An optional t'Proof' decoded from the URL; falls back to the first example proof.
  Maybe Proof ->
  Model
initialModelFOL uri mp =
  initialModel
    emptyProofFOL
    (Derivation (ParsedValid "⊤" (Opr "⊤" [])) (ParsedValid "(⊤I)" (RuleApplication "⊤I" [])))
    (fromMaybe initialP mp)
    exampleProofsFOL
    operatorsFOL
    infixPredsFOL
    quantifiersFOL
    rulesFOL
    uri
 where
  (_, initialP) : _ = exampleProofsFOL
