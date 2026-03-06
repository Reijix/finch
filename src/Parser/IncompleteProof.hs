module Parser.IncompleteProof where

import Data.Text qualified as T
import Fitch.Proof
import Parser.Util
import Text.Megaparsec (chunk, eof, manyTill, runParser, try)
import Text.Megaparsec.Char

{- |
Safely print a proof using control characters for easy parsing later on.
Legend of control characters:

* @\\31@ separates a formula from its rule application
* @\\30@ separates separate lines from each other
* @\\29@ encloses groups like @fs@, @ps@ and @c@
* @\\28@ encloses a proof
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

pIncompleteDerivation :: (Parser m) => m Derivation
pIncompleteDerivation = do
  f <- pText
  chunk "\31"
  r <- pText
  chunk "\30"
  pure $ Derivation (Unparsed f "") (Unparsed r "")

pIncompleteAssumption :: (Parser m) => m Assumption
pIncompleteAssumption = do
  f <- pText
  chunk "\31"
  r <- pText
  chunk "\30"
  pure (Unparsed f "", Unparsed r "")

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

parseIncompleteProof :: Text -> Maybe Proof
parseIncompleteProof = rightToMaybe . runParser (pIncompleteProof <* eof) ""
