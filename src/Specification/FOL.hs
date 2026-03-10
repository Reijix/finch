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
import Fitch.Proof (
  AssumptionSpec (..),
  FormulaSpec (..),
  Proof (..),
  RuleSpec (..),
  TermSpec (TPlaceholder, TVar),
  (~>),
 )
import Parser.Proof (parseProof)
import Specification.Prop

operatorsFOL :: [(Text, Text, Int)]
operatorsFOL = operatorsProp

infixPredsFOL :: [(Text, Text)]
infixPredsFOL = [("", "=")]

quantifiersFOL :: [(Text, Text)]
quantifiersFOL = [("forall", "∀"), ("exists", "∃")]

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

readProof :: Text -> Proof
readProof proofText = case parseProof operatorsFOL infixPredsFOL quantifiersFOL proofText of
  Left err -> error $ "Could not parse proof:\n" <> proofText <> "\nError:\n" <> err
  Right p -> p

emptyProofFOL :: Proof
emptyProofFOL =
  readProof
    """
    |---
    |⊤ (⊤I)
    """

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

initialModelFOL :: URI -> Maybe Proof -> Model
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
