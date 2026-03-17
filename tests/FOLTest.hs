{-# LANGUAGE MultilineStrings #-}

{- |
Module      : FOLTest
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (GHC extensions)

HUnit tests for FOL t'Proof's.

Each HUnit test is a proof written in a @.fitch@ file and then checked for (in-)correctness.
There are three kinds of tests, each contained in their own folder:

* __Valid proofs__ (@tests\/ValidProofs\/@) — tests that the whole t'Proof' is valid, i.e.
everything is parsed correctly and every t'RuleApplication' can be verified.
* __Invalid rules__ (@tests\/InvalidRules\/@) — tests that the file contains
a wrongful t'RuleApplication'. The offending line number is encoded into the filename via
a @%@, e.g.:

> tests/InvalidRules/eqE1%3.fitch
* __Invalid formulae__ (@tests\/InvalidFormulae\/@) — same as invalid rules, but checks
that a formulae is invalid. This can either verify parse errors or freshness violations.
-}
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

------------------------------------------------------------------------------------------

-- * IO Helpers

{- | Returns the full paths of every entry inside the given directory.

Each filename returned by 'listDirectory' is prefixed with the supplied
directory path @fp@.
-}
pathsInDir :: FilePath -> IO [FilePath]
pathsInDir fp = map (fp <>) <$> listDirectory fp

{- | Reads, parses, and fully verifies a FOL t'Proof' from a file on disk.

1. The file is read as a 'ByteString' and decoded as UTF-8.
2. The contents are parsed with 'parseProof'.
3. The parsed t'Proof' is checked with 'checkProof' using a dummy 'initialModelFOL'

Returns the checked t'Proof' or fails with a parse failure.
-}
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
          (initialModelFOL (URI "" "" mempty) (Just p) True)

------------------------------------------------------------------------------------------

-- * Assertion Helpers

-- | Asserts that a t'Wrapper' value is semantically valid.
assertValid :: Wrapper a -> Assertion
assertValid (Unparsed _ err) =
  assertFailure . toString $
    "Parse error: " <> err
assertValid (ParsedInvalid _ err _) =
  assertFailure . toString $
    "Error: " <> err
assertValid _ = pass

-- | Asserts that a t'Wrapper' value is semantically invalid.
assertInvalid :: Wrapper a -> Assertion
assertInvalid (Unparsed _ err) =
  assertFailure . toString $
    "Parse error: " <> err
assertInvalid f@(ParsedValid txt _) =
  assertFailure . toString $
    "Expected invalid, but found valid: " <> txt
assertInvalid _ = pass

------------------------------------------------------------------------------------------

-- * Proof Expectations

{- | Traverses every line of a t'Proof' and asserts that each formula and
rule application is 'ParsedValid'.

Uses 'pFoldLinesM' to fold over assumptions and derivations in order:
-}
expectValidProof :: Proof -> Assertion
expectValidProof =
  pFoldLinesM
    (\_ (a, _) -> assertValid a)
    (\_ (Derivation f r) -> assertValid f >> assertValid r)
    ()

{- | Asserts that the t'RuleApplication' at line @n@ of a t'Proof' is
'ParsedInvalid'.
-}
expectInvalidRuleAt :: Int -> Proof -> Assertion
expectInvalidRuleAt n p = case pIndex n p of
  Just (Right (Derivation _ r)) -> assertInvalid r
  _ -> assertFailure "expectInvalidRuleAt: pIndex failed or found unexpected assumption!"

{- | Asserts that the t'Formula' at line @n@ of a
t'Proof' is 'ParsedInvalid'.
-}
expectInvalidFormulaAt :: Int -> Proof -> Assertion
expectInvalidFormulaAt n p = case pIndex n p of
  Just (Right (Derivation f _)) -> assertInvalid f
  Just (Left (a, _)) -> assertInvalid a
  _ -> assertFailure "expectInvalidFormulaAt: internal error, pIndex failed!"

------------------------------------------------------------------------------------------

-- * Tests

{- | Reads every proof file in @tests\/ValidProofs\/@ and asserts that the
entire t'Proof' is valid using 'expectValidProof.
-}
testValidProofs :: TestTree
testValidProofs =
  testCaseSteps "Testing valid proofs" $ \step ->
    mapM_
      ( (\str -> step str >> pure str)
          >=> readProof
          >=> expectValidProof
      )
      =<< pathsInDir "tests/ValidProofs/"

{- | Reads every proof file in @tests\/InvalidRules\/@ and asserts that the
  t'RuleApplication' at the line number encoded in the filename is v'ParsedInvalid'
using 'expectInvalidRuleAt'.
-}
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

{- | Reads every proof file in @tests\/InvalidFormulae\/@ and asserts that the
t'Formula' at the line number encoded in the filename is v'ParsedInvalid'
using 'expectInvalidFormulaAt'.
-}
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

-- | t'TestTree' for all tests related to "Fitch.Verification"
verificationTests :: TestTree
verificationTests =
  testGroup
    "Testing proof verification"
    [testValidProofs, testInvalidFormulae, testInvalidRules]
