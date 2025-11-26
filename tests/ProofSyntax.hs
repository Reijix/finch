module ProofSyntax where

import Control.Monad
import Data.Functor
import Data.List qualified as L
import Data.Maybe (fromJust, fromMaybe, isJust)
import Data.Text (pack)
import Fitch.Proof
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC

--------------------------------------------
-- UNIT TESTS

-- Definitions for unit testing:

formula :: Int -> ParseWrapper Formula
formula n = Parsed "" $ Predicate (pack $ show n) []

rule :: Int -> [Reference] -> ParseWrapper RuleApplication
rule str ref = Parsed "" (RuleApplication (Rule "Rule" [] (Predicate "Formula" [])) ref)

derivation :: Int -> Derivation
derivation n = Derivation (formula n) (rule n [])

line :: Int -> Proof
line n = ProofLine (derivation n)

-- example proof for removing a line
exProof0 :: Proof
exProof0 =
  SubProof
    [formula 0, formula 1]
    [ SubProof [formula 2] [line 3] (derivation 4)
    ]
    (derivation 5)

-- example proof that triggered an edge case
exProof1 :: Proof
exProof1 =
  SubProof
    [formula 0]
    [line 1, SubProof [formula 2, formula 3] [line 4, line 5] (derivation 6)]
    (derivation 7)

-- example proof that triggered another edge case
exProof2 :: Proof
exProof2 =
  SubProof
    []
    [ SubProof [] [line 0, line 1] $ derivation 2,
      SubProof
        [formula 3, formula 4]
        [line 5, line 6, line 7]
        (derivation 8)
    ]
    (derivation 9)

exProof3 :: Proof
exProof3 = SubProof [] [SubProof [formula 0] [line 1] (derivation 2), line 3] (derivation 4)

--------------------------------------------
-- PROPERTIES
instance Arbitrary Formula where
  arbitrary :: Gen Formula
  arbitrary = return $ Predicate "Formula" []

instance Arbitrary Rule where
  arbitrary :: Gen Rule
  arbitrary = fmap (Rule "Rule" []) arbitrary

instance Arbitrary RuleApplication where
  arbitrary :: Gen RuleApplication
  arbitrary = liftM2 RuleApplication arbitrary (pure [])

instance (Arbitrary a) => Arbitrary (ParseWrapper a) where
  arbitrary :: Gen (ParseWrapper a)
  arbitrary = fmap (Parsed "") arbitrary

instance Arbitrary Derivation where
  arbitrary :: Gen Derivation
  arbitrary = liftM2 Derivation arbitrary arbitrary

instance Arbitrary Proof where
  arbitrary :: Gen Proof
  arbitrary = sized proof'
    where
      proof' :: Int -> Gen Proof
      proof' 0 = fmap ProofLine arbitrary
      proof' n | n > 0 = oneof [fmap ProofLine arbitrary, liftM3 SubProof arbitrary ps arbitrary]
        where
          ps :: Gen [Proof]
          ps = do
            l <- chooseInt (1, 8)
            vectorOf l (proof' (n `div` 2))

data AddrKind = AssumptionKind | LineKind | ProofKind | ConclusionKind | AnyKind

arbitraryNodeAddrFor :: Proof -> AddrKind -> Gen NodeAddr
arbitraryNodeAddrFor (ProofLine {}) _ = discard -- return $ NAProof 0 Nothing
arbitraryNodeAddrFor (SubProof fs ps l) ak = case (fs, ak) of
  ([], AssumptionKind) -> discard
  ([], AnyKind) -> oneof [naLine ps, naSubProof AnyKind, naConclusion]
  (_, AssumptionKind) -> oneof [naAssumption, naSubProof AssumptionKind]
  (_, LineKind) -> oneof [naLine ps, naSubProof LineKind]
  (_, ProofKind) -> oneof [naProof ps, naSubProof ProofKind]
  (_, ConclusionKind) -> oneof [naConclusion, naSubProof ConclusionKind]
  (_, AnyKind) -> oneof [naAssumption, naLine ps, naSubProof AnyKind, naConclusion]
  where
    naConclusion = return NAConclusion
    naLine ps = maybe discard (`NAProof` Nothing) <$> suchThatMaybe (chooseInt (0, L.length ps - 1)) (\n -> isProofLine $ ps !! n)
    naProof ps = maybe discard (`NAProof` Nothing) <$> suchThatMaybe (chooseInt (0, L.length ps - 1)) (\n -> isSubProof $ ps !! n)
    naAssumption = fmap NAAssumption (chooseInt (0, L.length fs - 1))
    naSubProof ak = do
      mn <- chooseInt (0, L.length ps - 1) `suchThatMaybe` (\n -> isSubProof $ ps !! n)
      case mn of
        Nothing -> discard
        Just n -> arbitraryNodeAddrFor (ps !! n) ak <&> (NAProof n . Just)

prop_lRemoveMinus1 :: Proof -> Property
prop_lRemoveMinus1 (ProofLine {}) = discard
prop_lRemoveMinus1 p@(SubProof {}) =
  forAll (arbitraryNodeAddrFor p LineKind) $ \a ->
    lLength (lRemove a p) === lLength p - 1

prop_lRemoveShift :: Proof -> Property
prop_lRemoveShift p =
  forAll (arbitraryNodeAddrFor p LineKind) $ \a ->
    lIsLine (incrementNodeAddr a) p ==>
      lLookup a (lRemove a p) === lLookup (incrementNodeAddr a) p

lRemoveQCTests :: TestTree
lRemoveQCTests =
  testGroup
    "Testing lRemove"
    [ QC.testProperty "prop_lRemoveMinus1" prop_lRemoveMinus1,
      QC.testProperty "prop_lRemoveShift" prop_lRemoveShift
    ]

-- TESTING lInsert
prop_lInsertBeforeFormulaPlus1 :: Proof -> Property
prop_lInsertBeforeFormulaPlus1 (ProofLine {}) = discard
prop_lInsertBeforeFormulaPlus1 p@(SubProof {}) =
  forAll (arbitraryNodeAddrFor p AssumptionKind) $ \a ->
    lLength (fromJust (lInsert (Left $ formula 0) a Before p)) === lLength p + 1

prop_lInsertAfterFormulaPlus1 :: Proof -> Property
prop_lInsertAfterFormulaPlus1 p =
  forAll (arbitraryNodeAddrFor p AssumptionKind) $ \a ->
    lLength (fromJust (lInsert (Left $ formula 0) a After p)) === lLength p + 1

prop_lInsertlLookupFormulaBefore :: Proof -> Property
prop_lInsertlLookupFormulaBefore p =
  forAll (arbitraryNodeAddrFor p AssumptionKind) $ \a ->
    lLookup a (fromJust (lInsert (Left $ formula 0) a Before p)) === Just (Left $ formula 0)

prop_lInsertlLookupFormulaAfter :: Proof -> Property
prop_lInsertlLookupFormulaAfter p =
  forAll (arbitraryNodeAddrFor p AssumptionKind) $ \a ->
    lLookup (incrementNodeAddr a) (fromJust (lInsert (Left $ formula 0) a After p)) === Just (Left $ formula 0)

prop_lInsertBeforeLinePlus1 :: Proof -> Property
prop_lInsertBeforeLinePlus1 p =
  forAll (arbitraryNodeAddrFor p LineKind) $ \a ->
    lLength (fromJust (lInsert (Right . ProofLine $ derivation 0) a Before p)) === lLength p + 1

prop_lInsertAfterLinePlus1 :: Proof -> Property
prop_lInsertAfterLinePlus1 p =
  forAll (arbitraryNodeAddrFor p LineKind) $ \a ->
    lLength (fromJust (lInsert (Right . ProofLine $ derivation 0) a After p)) === lLength p + 1

lInsertQCTests :: TestTree
lInsertQCTests =
  testGroup
    "Testing lInsert"
    [ QC.testProperty "prop_lInsertBeforeFormulaPlus1" prop_lInsertBeforeFormulaPlus1,
      QC.testProperty "prop_lInsertAfterFormulaPlus1" prop_lInsertAfterFormulaPlus1,
      QC.testProperty "prop_lInsertlLookupFormulaBefore" prop_lInsertlLookupFormulaBefore,
      QC.testProperty "prop_lInsertlLookupFormulaAfter" prop_lInsertlLookupFormulaAfter,
      QC.testProperty "prop_lInsertBeforeLinePlus1" prop_lInsertBeforeLinePlus1,
      QC.testProperty "prop_lInsertAfterLinePlus1" prop_lInsertAfterLinePlus1
    ]

prop_fromLineNoInverse :: Proof -> Property
prop_fromLineNoInverse p = forAll (chooseInt (0, lLength p - 1)) $ \n ->
  isJust (fromLineNo n p) ==>
    fromNodeAddr (fromJust $ fromLineNo n p) p === Just n

prop_fromNodeAddrInverse :: Proof -> Property
prop_fromNodeAddrInverse p = forAll (arbitraryNodeAddrFor p AnyKind) $ \a ->
  isJust (fromNodeAddr a p) ==>
    fromLineNo (fromJust $ fromNodeAddr a p) p === Just a

lineNoQCTests :: TestTree
lineNoQCTests =
  testGroup
    "testing conversion of lineNo and NodeAddr"
    [ QC.testProperty "prop_fromLineNoInverse" prop_fromLineNoInverse,
      QC.testProperty "prop_fromNodeAddrInverse" prop_fromNodeAddrInverse
    ]

prop_compareLineNo :: Proof -> Property
prop_compareLineNo p =
  forAll (arbitraryNodeAddrFor p AnyKind) $ \a ->
    forAll (arbitraryNodeAddrFor p AnyKind) $ \b ->
      isJust (fromNodeAddr a p) ==>
        isJust (fromNodeAddr b p) ==>
          compare a b === compare (fromJust $ fromNodeAddr a p) (fromJust $ fromNodeAddr b p)

compareQCTests :: TestTree
compareQCTests =
  testGroup
    "testing compare instance of NodeAddr"
    [QC.testProperty "prop_compareLineNo" prop_compareLineNo]

proofTests :: TestTree
proofTests =
  testGroup
    "Testing functions concerning the modification of proofs"
    [ testGroup "QuickCheck" [lRemoveQCTests, lInsertQCTests, lineNoQCTests, compareQCTests],
      testGroup "HUnit" []
    ]