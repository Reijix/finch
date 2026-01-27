module FOLTest where

import Fitch.Proof
import Fitch.Verification (verifyProof)
import Parser.Formula (parseFormula)
import Parser.Proof (parseProof)
import Specification.FOL
import System.Directory (listDirectory)
import Test.Tasty (TestTree, testGroup)
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
    Right p -> pure $ verifyProof rulesFOL p

assertValid :: Wrapper a -> Assertion
assertValid (Unparsed _ err) =
  assertFailure . toString $
    "Parse error: " <> err
assertValid (ParsedInvalid _ err _) =
  assertFailure . toString $
    "Error: " <> err
assertValid _ = pass

assertInvalid :: Wrapper a -> Assertion
assertInvalid (Unparsed _ err) =
  assertFailure . toString $
    "Parse error: " <> err
assertInvalid (ParsedValid txt _) =
  assertFailure . toString $
    "Expected invalid, but found valid: " <> txt
assertInvalid _ = pass

assertProofValid :: Proof -> Assertion
assertProofValid =
  pFoldM
    (const assertValid)
    (\_ (Derivation f r) -> assertValid f >> assertValid r)
    ()

assertProofInvalidAt :: Int -> Proof -> Assertion
assertProofInvalidAt n p = case pIndex n p of
  Just (Right (Derivation _ r)) -> assertInvalid r
  _ ->
    assertFailure . toString $
      "assertProofInvalidAt: indexing line "
        <> show n
        <> " went wrong for proof:\n"
        <> prettyPrint p

testValidProofs :: TestTree
testValidProofs =
  testCaseSteps "Testing valid proofs" $ \step ->
    mapM_
      ( (\str -> step str >> pure str)
          >=> readProof
          >=> assertProofValid
      )
      =<< pathsInDir "tests/ValidProofs/"

testInvalidProofs :: TestTree
testInvalidProofs =
  testCaseSteps "Testing invalid proofs" $ \step ->
    mapM_
      ( \(fp, n) ->
          step fp
            >> readProof ("tests/InvalidProofs/" <> fp)
            >>= assertProofInvalidAt n
      )
      [("eqE1.fitch", 3), ("eqE2.fitch", 3)]

verificationTests :: TestTree
verificationTests =
  testGroup
    "Testing proof verification"
    [testValidProofs, testInvalidProofs]