{-# LANGUAGE CPP #-}
{-# LANGUAGE InstanceSigs #-}

module Main where

import App
import App.Syntax
import Proof.Syntax

-----------------------------------------------------------------------------
main :: IO ()
main = runApp emptyModel

-----------------------------------------------------------------------------
data Rule = Rule deriving (Show, Eq)

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

-- exProof :: Proof Formula Rule
-- exProof =
--   SubProof
--     []
--     [ProofLine (Derivation (Formula "line1") Rule []), ProofLine (Derivation (Formula "line2") Rule [])]
--     (Derivation (Formula "conclusion") Rule [])

exProof :: (Proof Formula Rule)
exProof =
  SubProof
    [Formula "Formula", Formula "Formula"]
    [ ProofLine (Derivation (Formula "Formula") Rule []),
      SubProof [Formula "Formula"] [ProofLine (Derivation (Formula "Formula") Rule [])] (Derivation (Formula "Formula") Rule []),
      SubProof [Formula "Formula"] [ProofLine (Derivation (Formula "Formula") Rule [])] (Derivation (Formula "Formula") Rule [])
    ]
    (Derivation (Formula "Formula") Rule [])

-----------------------------------------------------------------------------
