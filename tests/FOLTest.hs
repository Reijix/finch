module FOLTest where

import App.Model
import App.Runner
import Fitch.Proof
import Fitch.Verification (verifyProof)
import Parser.Formula (parseFormula)
import Parser.Proof (parseProof)
import Specification.FOL
import System.Directory (listDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

import Miso.Lens ((^.))

pathsInDir :: FilePath -> IO [FilePath]
pathsInDir fp = map (fp <>) <$> listDirectory fp

readProof :: String -> IO Proof
readProof filePath = do
  contents <- readFileBS filePath
  case parseProof operatorsFOL infixPredsFOL quantifiersFOL (decodeUtf8 contents) of
    Left err ->
      assertFailure . toString $
        "Could not parse file " <> err <> "\n" <> err
    Right p -> pure . (^. proof) $ execState checkProof (initialModel p operatorsFOL infixPredsFOL quantifiersFOL rulesFOL)

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
assertInvalid f@(ParsedValid txt _) =
  assertFailure . toString $
    "Expected invalid, but found valid: " <> txt
assertInvalid _ = pass

expectValidProof :: Proof -> Assertion
expectValidProof =
  pFoldLinesM
    (const assertValid)
    (\_ (Derivation f r) -> assertValid f >> assertValid r)
    ()

expectInvalidRuleAt :: Int -> Proof -> Assertion
expectInvalidRuleAt n p = case pIndex n p of
  Just (Right (Derivation _ r)) -> assertInvalid r
  _ -> assertFailure "expectInvalidRuleAt: pIndex failed or found unexpected assumption!"

expectInvalidFormulaAt :: Int -> Proof -> Assertion
expectInvalidFormulaAt n p = case pIndex n p of
  Just (Right (Derivation f _)) -> assertInvalid f
  Just (Left f) -> assertInvalid f
  _ -> assertFailure "expectInvalidFormulaAt: internal error, pIndex failed!"

testValidProofs :: TestTree
testValidProofs =
  testCaseSteps "Testing valid proofs" $ \step ->
    mapM_
      ( (\str -> step str >> pure str)
          >=> readProof
          >=> expectValidProof
      )
      =<< pathsInDir "tests/ValidProofs/"

testInvalidProofs :: TestTree
testInvalidProofs =
  testCaseSteps "Testing invalid proofs" $ \step ->
    mapM_
      ( \(fp, fun) ->
          step fp
            >> readProof ("tests/InvalidProofs/" <> fp)
            >>= fun
      )
      [ ("eqE1.fitch", expectInvalidRuleAt 3)
      , ("eqE2.fitch", expectInvalidRuleAt 3)
      , ("notFresh.fitch", expectInvalidFormulaAt 3)
      ]

verificationTests :: TestTree
verificationTests =
  testGroup
    "Testing proof verification"
    [testValidProofs, testInvalidProofs]