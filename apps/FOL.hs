{-# LANGUAGE CPP #-}

module FOL where

import App
import App.Syntax
import Proof.Syntax

-----------------------------------------------------------------------------
#ifdef WASM
foreign export javascript "hs_start" main :: IO ()
#endif
-----------------------------------------------------------------------------
main :: IO ()
main = runApp emptyModel

-----------------------------------------------------------------------------
data Rule = Rule deriving (Show, Eq)

type Formula = String

-----------------------------------------------------------------------------
emptyModel :: (Model Formula Rule)
emptyModel =
  Model
    { _cursorX = 50,
      _cursorY = 52,
      _focusedLine = Nothing,
      _proof = exProof,
      _dragTarget = Nothing,
      _currentLineBefore = Nothing,
      _currentLineAfter = Nothing,
      _dragging = False
    }

exProof :: (Proof Formula Rule)
exProof =
  SubProof
    ["Formula", "Formula"]
    [ SubProof ["Formula"] [ProofLine (Derivation "Formula" Rule [])] (Derivation "Formula" Rule [])
    ]
    (Derivation "Formula" Rule [])

-----------------------------------------------------------------------------
