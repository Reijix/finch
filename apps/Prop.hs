{-# LANGUAGE MultilineStrings #-}

module Main where

import App.Model (operators)
import App.Runner
import Data.Map qualified as M
import Data.Text
import Fitch.Proof
import Parser.Proof (parseProof)
import Specification.Prop

-----------------------------------------------------------------------------
main :: IO ()
main = runApp exProof operatorsProp [] [] rulesProp
 where
  exProof :: Proof
  exProof = case parseProof operatorsProp [] [] proofText of
    Left err -> error "Could not parse initial proof!"
    Right p -> p
  proofText :: Text
  proofText =
    """
    | A
    | A → B
    |---
    | B      (→E) 1,2
    """

-----------------------------------------------------------------------------