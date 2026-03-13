{-# LANGUAGE CPP #-}

{- |
Module      : Main
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)
-}
module Main where

import App.Entry

------------------------------------------------------------------------------------------

-- | WASM export, required when compiling w/ the WASM backend.
#ifdef WASM
foreign export javascript "hs_start" main :: IO ()
#endif

main :: IO ()
main = runApp
