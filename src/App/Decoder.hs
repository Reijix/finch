module App.Decoder where

import Data.ByteString.Base64.URL qualified as Base64URL
import Data.Serialize (Get, Putter, Serialize (..), decode, encode)
import Data.Serialize.Text
import Fitch.Proof
import Prelude hiding (get, put)

-- Automatically derive serialization

instance Serialize Term
instance Serialize RawFormula
instance Serialize RawAssumption
instance (Serialize a) => Serialize (Wrapper a)
instance Serialize Reference
instance Serialize RuleApplication
instance Serialize Derivation
instance Serialize Proof

-- | Encodes a data structure to a URL-safe Text
encodeForUrl :: (Serialize a) => a -> Text
encodeForUrl = decodeUtf8 . Base64URL.encode . encode

-- | Decodes a URL-safe Text back into your data structure
decodeFromUrl :: (Serialize a) => Text -> Either Text a
decodeFromUrl urlText = maybeToRight "Failed to parse from url" $ do
  bs <- rightToMaybe (Base64URL.decode $ encodeUtf8 urlText)
  rightToMaybe (decode bs)
