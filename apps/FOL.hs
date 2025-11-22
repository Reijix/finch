{-# LANGUAGE CPP #-}
{-# LANGUAGE InstanceSigs #-}

module Main where

import App.Runner
import Fitch.Proof (ParseWrapper (..), Reference, RuleApplication (RuleApplication))

-----------------------------------------------------------------------------
main :: IO ()
main = runApp emptyModel

-----------------------------------------------------------------------------
newtype Rule = Rule String deriving (Show, Eq)

newtype Formula = Formula String deriving (Eq)

instance Show Formula where
  show :: Formula -> String
  show (Formula str) = str

instance FromString Formula where
  fromString :: String -> Either Formula String
  fromString = Left . Formula

-----------------------------------------------------------------------------
emptyModel :: (Model Formula Rule)
emptyModel =
  Model
    { _cursorX = 50,
      _cursorY = 52,
      _focusedLine = Nothing,
      _proof = exProof,
      _spawnType = Nothing,
      _dragTarget = Nothing,
      _currentLineBefore = Nothing,
      _currentLineAfter = Nothing,
      _dragging = False
    }

formula :: String -> ParseWrapper Formula
formula = Parsed . Formula

rule :: String -> [Reference] -> ParseWrapper (RuleApplication Rule)
rule str ref = Parsed (RuleApplication (Rule str) ref)

exProof :: (Proof Formula Rule)
exProof =
  SubProof
    [formula "Formula", formula "Formula"]
    [ ProofLine (Derivation (formula "Formula") (rule "rule" [])),
      SubProof [formula "Formula"] [ProofLine (Derivation (formula "Formula") (rule "rule" []))] (Derivation (formula "Formula") (rule "rule" [])),
      SubProof [formula "Formula"] [ProofLine (Derivation (formula "Formula") (rule "rule" []))] (Derivation (formula "Formula") (rule "rule" []))
    ]
    (Derivation (formula "Formula") (rule "rule" []))

-----------------------------------------------------------------------------
