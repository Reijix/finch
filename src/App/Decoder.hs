module App.Decoder where

import Data.Base64.Types (extractBase64)
import Data.Text.Encoding.Base64.URL qualified as Base64URL
import Fitch.Proof
import Parser.IncompleteProof

-- | Encodes `Proof` to a URL-safe Text
encodeForUrl :: Proof -> Text
encodeForUrl = extractBase64 . Base64URL.encodeBase64 . safeParsePrint

-- | Decodes a URL-safe Text back to `Proof`
decodeFromUrl :: Text -> Maybe Proof
decodeFromUrl = parseIncompleteProof . Base64URL.decodeBase64Lenient
