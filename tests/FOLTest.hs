module FOLTest where

import Fitch.Proof
import Parser.Formula (parseFormula)
import Parser.Proof
import Specification.FOL
import System.Directory
import Test.Tasty
import Test.Tasty.HUnit

pathsInDir :: FilePath -> IO [FilePath]
pathsInDir fp = map (fp <>) <$> listDirectory fp

readProof :: String -> IO Proof
readProof filePath = do
  contents <- readFileBS filePath
  case parseProof operatorsFOL infixPredsFOL quantifiersFOL (decodeUtf8 contents) of
    Left err ->
      assertFailure . toString $
        "Could not parse file " <> err <> "\n" <> err
    Right p -> pure p

assertProofValid :: Proof -> Assertion
assertProofValid = pFoldM assumptionGo derivationGo ()
 where
  assumptionGo :: () -> Assumption -> Assertion
  assumptionGo _ (Unparsed _ err) =
    assertFailure . toString $
      "Parse error: " <> err
  assumptionGo _ (ParsedInvalid _ err _) =
    assertFailure . toString $
      "Error: " <> err
  assumptionGo _ _ = pass
  derivationGo :: () -> Derivation -> Assertion
  derivationGo _ (Derivation (Unparsed _ err) _) =
    assertFailure . toString $
      "Parse error in formula: " <> err
  derivationGo _ (Derivation _ (Unparsed _ err)) =
    assertFailure . toString $
      "Parse error in rule: " <> err
  derivationGo _ (Derivation (ParsedInvalid _ err _) _) =
    assertFailure . toString $
      "Error in formula: " <> err
  derivationGo _ (Derivation _ (ParsedInvalid _ err _)) =
    assertFailure . toString $
      "Error in rule: " <> err
  derivationGo _ _ = pass

testValidProofs :: TestTree
testValidProofs =
  testCaseSteps "Testing valid proofs" $ \step ->
    mapM_ ((\str -> step str >> pure str) >=> readProof >=> assertProofValid) =<< pathsInDir "tests/ValidProofs/"

verificationTests :: TestTree
verificationTests =
  testGroup
    "Testing proof verification"
    [testValidProofs]