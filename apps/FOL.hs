{-# LANGUAGE MultilineStrings #-}

module Main where

import App.Model (operators)
import App.Runner
import Data.Map qualified as M
import Data.Text
import Fitch.Proof
import Parser.Proof (parseProof)
import Specification.FOL

-----------------------------------------------------------------------------
main :: IO ()
main = runApp exProof operatorsFOL infixPredsFOL quantifiersFOL rulesFOL
 where
  exProof :: Proof
  exProof = case parseProof operatorsFOL infixPredsFOL quantifiersFOL proofText of
    Left err -> error "Could not parse initial proof!"
    Right p -> p
  proofText :: Text
  proofText =
    """
    |∃x.P(x)
    |---
    ||[c]
    ||P(c)
    ||---
    ||P(c) (R) 3
    |P(c) (∃E) 1, 2-4
    """

-- """
-- \|∀x. P(x) → Q(x)
-- \|∀z. Q(z) → R(z)
-- \|---
-- \||[d]
-- \||---
-- \|||P(d)
-- \|||---
-- \|||P(d) → Q(d)        (∀E) 1
-- \|||Q(d)               (→E) 4,5
-- \|||Q(d) → R(d)        (∀E) 2
-- \|||R(d)               (→E) 6,7
-- \||P(d) → R(d)         (→I) 4-8
-- \|P(x)                 (=I)
-- \|x = t                (=I)
-- \|P(t)                 (=E) 10,11

-- """

-----------------------------------------------------------------------------