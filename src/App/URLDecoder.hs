{- |
Module      : App.URLDecoder
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module defines function for encoding a t'Proof' as URL-safe Base64
and also decoding back to a t'Proof'.
-}
module App.URLDecoder where

import Data.Base64.Types (extractBase64)
import Data.Text.Encoding.Base64.URL qualified as Base64URL
import Fitch.Proof (Proof)
import Parser.IncompleteProof (parseIncompleteProof, safeParsePrint)

-- | Encodes t'Proof' to a URL-safe 'Text'
encodeForUrl :: Proof -> Text
encodeForUrl = extractBase64 . Base64URL.encodeBase64 . safeParsePrint

-- | Decodes a URL-safe 'Text' back to t'Proof'
decodeFromUrl :: Text -> Maybe Proof
decodeFromUrl = parseIncompleteProof . Base64URL.decodeBase64Lenient
