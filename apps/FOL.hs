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
    |∀x. P(x) → Q(x)
    |∀z. Q(z) → R(z)
    |---
    ||P(d)
    ||---
    ||P(d) → Q(d)        (∀E) 1
    ||Q(d)               (→E) 3,4
    ||Q(d) → R(d)        (∀E) 2
    ||R(d)               (→E) 5,6
    ||[d]
    ||---
    ||P(d) → R(d)         (→I) 3-7
    |∀x.P(x) → R(c)       (∀I) 8-9
    """

-----------------------------------------------------------------------------