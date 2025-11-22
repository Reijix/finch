module ProofSyntax where

import Control.Monad
import Data.Functor
import Data.List qualified as L
import Data.Maybe (fromJust, fromMaybe, isJust)
import Fitch.Proof
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC

--------------------------------------------
-- UNIT TESTS

-- Definitions for unit testing:

derivation :: Int -> Derivation Formula Rule
derivation n = Derivation (Formula n) (Rule n) []

line :: Int -> Proof Formula Rule
line n = ProofLine (derivation n)

-- example proof for removing a line
exProof0 :: Proof Formula Rule
exProof0 =
  SubProof
    [Formula 0, Formula 1]
    [ SubProof [Formula 2] [line 3] (derivation 4)
    ]
    (derivation 5)

-- example proof that triggered an edge case
exProof1 :: Proof Formula Rule
exProof1 =
  SubProof
    [Formula 0]
    [line 1, SubProof [Formula 2, Formula 3] [line 4, line 5] (derivation 6)]
    (derivation 7)

-- example proof that triggered another edge case
exProof2 :: Proof Formula Rule
exProof2 =
  SubProof
    []
    [ SubProof [] [line 0, line 1] $ derivation 2,
      SubProof
        [Formula 3, Formula 4]
        [line 5, line 6, line 7]
        (derivation 8)
    ]
    (derivation 9)

exProof3 :: Proof Formula Rule
exProof3 = SubProof [] [SubProof [Formula 0] [line 1] (derivation 2), line 3] (derivation 4)

--------------------------------------------
-- PROPERTIES
newtype Formula = Formula Int deriving (Eq)

newtype Rule = Rule Int deriving (Eq)

instance Show Formula where
  show :: Formula -> String
  show (Formula n) = 'F' : show n

instance Show Rule where
  show :: Rule -> String
  show (Rule n) = 'R' : show n

instance Arbitrary Formula where
  arbitrary :: Gen Formula
  arbitrary = fmap Formula (chooseInt (0, 100))

instance Arbitrary Rule where
  arbitrary :: Gen Rule
  arbitrary = fmap Rule (chooseInt (0, 100))

instance Arbitrary (Derivation Formula Rule) where
  arbitrary :: Gen (Derivation Formula Rule)
  arbitrary = liftM3 Derivation arbitrary arbitrary (pure [])

instance Arbitrary (Proof Formula Rule) where
  arbitrary :: Gen (Proof Formula Rule)
  arbitrary = sized proof'
    where
      proof' :: Int -> Gen (Proof Formula Rule)
      proof' 0 = fmap ProofLine arbitrary
      proof' n | n > 0 = oneof [fmap ProofLine arbitrary, liftM3 SubProof arbitrary ps arbitrary]
        where
          ps :: Gen [Proof Formula Rule]
          ps = do
            l <- chooseInt (1, 8)
            vectorOf l (proof' (n `div` 2))

data AddrKind = Assumption | Line | Proof | Conclusion | Any

arbitraryNodeAddrFor :: Proof Formula Rule -> AddrKind -> Gen NodeAddr
arbitraryNodeAddrFor (ProofLine {}) _ = discard -- return $ NAProof 0 Nothing
arbitraryNodeAddrFor (SubProof fs ps l) ak = case (fs, ak) of
  ([], Assumption) -> discard
  ([], Any) -> oneof [naLine ps, naSubProof Any, naConclusion]
  (_, Assumption) -> oneof [naAssumption, naSubProof Assumption]
  (_, Line) -> oneof [naLine ps, naSubProof Line]
  (_, Proof) -> oneof [naProof ps, naSubProof Proof]
  (_, Conclusion) -> oneof [naConclusion, naSubProof Conclusion]
  (_, Any) -> oneof [naAssumption, naLine ps, naSubProof Any, naConclusion]
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

prop_lRemoveMinus1 :: Proof Formula Rule -> Property
prop_lRemoveMinus1 (ProofLine {}) = discard
prop_lRemoveMinus1 p@(SubProof {}) =
  forAll (arbitraryNodeAddrFor p Line) $ \a ->
    lLength (lRemove a p) === lLength p - 1

prop_lRemoveShift :: Proof Formula Rule -> Property
prop_lRemoveShift p =
  forAll (arbitraryNodeAddrFor p Line) $ \a ->
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
prop_lInsertBeforeFormulaPlus1 :: Proof Formula Rule -> Property
prop_lInsertBeforeFormulaPlus1 (ProofLine {}) = discard
prop_lInsertBeforeFormulaPlus1 p@(SubProof {}) =
  forAll (arbitraryNodeAddrFor p Assumption) $ \a ->
    lLength (fromJust (lInsert (Left $ Formula 0) a Before p)) === lLength p + 1

prop_lInsertAfterFormulaPlus1 :: Proof Formula Rule -> Property
prop_lInsertAfterFormulaPlus1 p =
  forAll (arbitraryNodeAddrFor p Assumption) $ \a ->
    lLength (fromJust (lInsert (Left $ Formula 0) a After p)) === lLength p + 1

prop_lInsertlLookupFormulaBefore :: Proof Formula Rule -> Property
prop_lInsertlLookupFormulaBefore p =
  forAll (arbitraryNodeAddrFor p Assumption) $ \a ->
    lLookup a (fromJust (lInsert (Left $ Formula 0) a Before p)) === Just (Left $ Formula 0)

prop_lInsertlLookupFormulaAfter :: Proof Formula Rule -> Property
prop_lInsertlLookupFormulaAfter p =
  forAll (arbitraryNodeAddrFor p Assumption) $ \a ->
    lLookup (incrementNodeAddr a) (fromJust (lInsert (Left $ Formula 0) a After p)) === Just (Left $ Formula 0)

prop_lInsertBeforeLinePlus1 :: Proof Formula Rule -> Property
prop_lInsertBeforeLinePlus1 p =
  forAll (arbitraryNodeAddrFor p Line) $ \a ->
    lLength (fromJust (lInsert (Right . ProofLine $ Derivation (Formula 0) (Rule 0) []) a Before p)) === lLength p + 1

prop_lInsertAfterLinePlus1 :: Proof Formula Rule -> Property
prop_lInsertAfterLinePlus1 p =
  forAll (arbitraryNodeAddrFor p Line) $ \a ->
    lLength (fromJust (lInsert (Right . ProofLine $ Derivation (Formula 0) (Rule 0) []) a After p)) === lLength p + 1

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

prop_fromLineNoInverse :: Proof Formula Rule -> Property
prop_fromLineNoInverse p = forAll (chooseInt (0, lLength p - 1)) $ \n ->
  isJust (fromLineNo n p) ==>
    fromNodeAddr (fromJust $ fromLineNo n p) p === Just n

prop_fromNodeAddrInverse :: Proof Formula Rule -> Property
prop_fromNodeAddrInverse p = forAll (arbitraryNodeAddrFor p Any) $ \a ->
  isJust (fromNodeAddr a p) ==>
    fromLineNo (fromJust $ fromNodeAddr a p) p === Just a

lineNoQCTests :: TestTree
lineNoQCTests =
  testGroup
    "testing conversion of lineNo and NodeAddr"
    [ QC.testProperty "prop_fromLineNoInverse" prop_fromLineNoInverse,
      QC.testProperty "prop_fromNodeAddrInverse" prop_fromNodeAddrInverse
    ]

prop_compareLineNo :: Proof Formula Rule -> Property
prop_compareLineNo p =
  forAll (arbitraryNodeAddrFor p Any) $ \a ->
    forAll (arbitraryNodeAddrFor p Any) $ \b ->
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