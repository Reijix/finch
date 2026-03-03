{-# LANGUAGE MultilineStrings #-}

module Main where

import App.Model (operators)
import App.Runner
import Data.Map qualified as M
import Fitch.Proof
import Parser.Proof (parseProof)
import Specification.FOL

-----------------------------------------------------------------------------
main :: IO ()
main = runApp emptyProof exampleProofs operatorsFOL infixPredsFOL quantifiersFOL rulesFOL
 where
  readProof :: Text -> Proof
  readProof proofText = case parseProof operatorsFOL infixPredsFOL quantifiersFOL proofText of
    Left err -> error $ "Could not parse proof:\n" <> proofText <> "\nError:\n" <> err
    Right p -> p
  emptyProof :: Proof
  emptyProof =
    readProof
      """
      |---
      |⊤ (⊤I)
      """
  exampleProofs :: [(Text, Proof)]
  exampleProofs =
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
          ||||⊥       (¬E) 2,5
          |||¬P(c)    (¬I) 4-6
          ||∀x.¬P(x)  (∀I) 3-7
          ||⊥         (¬E) 1,8
          |¬¬∃x.φ     (¬I) 2-9
          |∃x.φ       (¬¬E) 10
          """
      )
    ]

-----------------------------------------------------------------------------