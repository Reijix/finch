{- |
Module      : Parser.IncompleteProof
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module defines a compact serialization format for t'Proof's using
ASCII control characters, and a corresponding parser for deserialization.
This format is used for encoding t'Proof's in URLs via
t'App.URLDecoder'.

In contrast to "Parser.Proof" this can also parse incomplete t'Proof's,
i.e. ones with parse errors.
-}
module Parser.IncompleteProof where

import Data.Text qualified as T
import Fitch.Proof
import Parser.Util
import Text.Megaparsec (chunk, eof, manyTill, runParser, try)
import Text.Megaparsec.Char

------------------------------------------------------------------------------------------

-- * Serialization

{- | Serializes a t'Proof' to a compact t'Text' representation using
ASCII control characters as delimiters, suitable for later re-parsing
with 'parseIncompleteProof'.

Legend of control characters:

* @\\31@ separates a t'Formula' from its t'RuleApplication'
* @\\30@ separates individual lines from each other
* @\\29@ encloses groups: the t'Assumption' list, the t'Derivation' or t'Proof' list,
and the conclusion
* @\\28@ encloses an entire t'Proof'
-}
safeParsePrint :: Proof -> Text
safeParsePrint (SubProof fs ps c) =
  "\28\29"
    <> fsShow
    <> "\29"
    <> psShow
    <> "\29"
    <> cShow
    <> "\29\28"
 where
  fsShow = T.concat $ map assumptionShow fs
  psShow = T.concat $ map (either derivationShow safeParsePrint) ps
  cShow = derivationShow c
  assumptionShow :: Assumption -> Text
  assumptionShow (a, r) = prettyPrint a <> "\31" <> prettyPrint r <> "\30"
  derivationShow :: Derivation -> Text
  derivationShow (Derivation f r) = prettyPrint f <> "\31" <> prettyPrint r <> "\30"

------------------------------------------------------------------------------------------

-- * Parsers

{- | Parses a single t'Derivation' from the serialization format produced by
'safeParsePrint'.
The t'Formula' and t'RuleApplication' fields are left as v'Unparsed'
wrappers and are re-parsed later by the application.
-}
pIncompleteDerivation :: (Parser m) => m Derivation
pIncompleteDerivation = do
  f <- pText
  chunk "\31"
  r <- pText
  chunk "\30"
  pure $ Derivation (Unparsed f "") (Unparsed r "")

{- | Parses a single t'Assumption' from the serialization format produced by
'safeParsePrint'.
Both the t'Formula' and t'RuleApplication' fields are left as v'Unparsed' wrappers
and are re-parsed later by the application.
-}
pIncompleteAssumption :: (Parser m) => m Assumption
pIncompleteAssumption = do
  f <- pText
  chunk "\31"
  r <- pText
  chunk "\30"
  pure (Unparsed f "", Unparsed r "")

-- | Parses a full t'Proof' from the serialization format produced by 'safeParsePrint'.
pIncompleteProof :: (Parser m) => m Proof
pIncompleteProof = do
  chunk "\28\29"
  fs <- manyTill pIncompleteAssumption (chunk "\29")
  ps <-
    manyTill
      (try (Right <$> pIncompleteProof) <|> (Left <$> pIncompleteDerivation))
      (chunk "\29")
  c <- pIncompleteDerivation
  chunk "\29\28"
  pure $ SubProof fs ps c

------------------------------------------------------------------------------------------

-- * Entry point

{- | Deserializes a t'Proof' from a t'Text' produced by 'safeParsePrint'.
Returns 'Nothing' if parsing fails.
-}
parseIncompleteProof :: Text -> Maybe Proof
parseIncompleteProof = rightToMaybe . runParser (pIncompleteProof <* eof) ""
