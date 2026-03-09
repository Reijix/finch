{-# LANGUAGE MultilineStrings #-}

module FOLTest where

import App.Model
import App.Update
import Fitch.Proof
import Fitch.Verification (verifyProof)
import Miso.Router (URI (..))
import Parser.Formula (parseFormula)
import Parser.Proof (parseProof)
import Specification.FOL
import System.Directory (listDirectory)
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit

import Miso.Lens ((^.))

exProof :: Proof
exProof = case parseProof operatorsFOL infixPredsFOL quantifiersFOL proofText of
  Left err -> error "Could not parse initial proof!"
  Right p -> p
proofText :: Text
proofText =
  """
  |Q(c)
  |---
  ||[c]
  ||---
  ||c = c (=I)
  |∀x.x=x (∀I) 2-3
  """

pathsInDir :: FilePath -> IO [FilePath]
pathsInDir fp = map (fp <>) <$> listDirectory fp

readProof :: String -> IO Proof
readProof filePath = do
  contents <- readFileBS filePath
  case parseProof operatorsFOL infixPredsFOL quantifiersFOL (decodeUtf8 contents) of
    Left err ->
      assertFailure . toString $
        "Could not parse file " <> err <> "\n" <> err
    Right p ->
      pure . (^. proof) $
        execState
          checkProof
          (initialModel p p [] operatorsFOL infixPredsFOL quantifiersFOL rulesFOL (URI "" "" mempty))

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
    (\_ (a, _) -> assertValid a)
    (\_ (Derivation f r) -> assertValid f >> assertValid r)
    ()

expectInvalidRuleAt :: Int -> Proof -> Assertion
expectInvalidRuleAt n p = case pIndex n p of
  Just (Right (Derivation _ r)) -> assertInvalid r
  _ -> assertFailure "expectInvalidRuleAt: pIndex failed or found unexpected assumption!"

expectInvalidFormulaAt :: Int -> Proof -> Assertion
expectInvalidFormulaAt n p = case pIndex n p of
  Just (Right (Derivation f _)) -> assertInvalid f
  Just (Left (a, _)) -> assertInvalid a
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

testInvalidRules :: TestTree
testInvalidRules =
  testCaseSteps "Testing invalid proofs" $ \step ->
    mapM_
      ( \str ->
          do
            let rem = dropWhile (/= '%') str
                lineNo = filter (/= '%') $ takeWhile (/= '.') rem
            step (str <> " at line " <> lineNo) >> pure (str, lineNo)
            p <- readProof str
            no :: Int <- case reads lineNo of
              [] -> fail $ "'reads' failed extracting a number from lineNo=" <> lineNo
              (n, _) : _ -> pure n
            expectInvalidRuleAt no p
      )
      =<< pathsInDir "tests/InvalidRules/"

testInvalidFormulae :: TestTree
testInvalidFormulae =
  testCaseSteps "Testing invalid proofs" $ \step ->
    mapM_
      ( \str ->
          do
            let rem = dropWhile (/= '%') str
                lineNo = filter (/= '%') $ takeWhile (/= '.') rem
            step (str <> " at line " <> lineNo) >> pure (str, lineNo)
            p <- readProof str
            no :: Int <- case reads lineNo of
              [] -> fail $ "'reads' failed extracting a number from lineNo=" <> lineNo
              (n, _) : _ -> pure n
            expectInvalidFormulaAt no p
      )
      =<< pathsInDir "tests/InvalidFormulae/"

verificationTests :: TestTree
verificationTests =
  testGroup
    "Testing proof verification"
    [testValidProofs, testInvalidRules]
