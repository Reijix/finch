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
    |P(d)                  (=I)
    ||---
    ||P(d)                 (=I)
    |∀x.P(x) → R(x)       (∀I) 3-9
    """

-----------------------------------------------------------------------------