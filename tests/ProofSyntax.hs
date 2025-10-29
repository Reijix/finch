module ProofSyntax where

import Control.Monad
import Data.Functor
import qualified Data.List as L
import Data.Maybe (fromJust, fromMaybe, isJust)
import Proof.Syntax
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

arbitraryNodeAddrFor :: Proof Formula Rule -> Gen NodeAddr
arbitraryNodeAddrFor (ProofLine {}) = return $ NALine 0
arbitraryNodeAddrFor (SubProof fs ps l) = case fs of
  [] -> oneof [naLine, naDeriv]
  _ -> oneof [naAssumption, naLine, naDeriv]
  where
    naLine = fmap NALine (chooseInt (0, L.length ps - 1))
    naAssumption = fmap NAAssumption (chooseInt (0, L.length fs - 1))
    naDeriv = do
      n <- chooseInt (0, L.length ps - 1)
      case ps !! n of
        ProofLine {} -> return $ NALine n
        p@(SubProof {}) -> arbitraryNodeAddrFor p <&> (NAProof n . Just)

prop_lRemoveMinus1 :: Proof Formula Rule -> Property
prop_lRemoveMinus1 (ProofLine {}) = discard
prop_lRemoveMinus1 p@(SubProof {}) =
  forAll (arbitraryNodeAddrFor p) $ \a ->
    lIsLine a p ==>
      lLength (lRemove a p) === lLength p - 1

prop_lRemoveShift :: Proof Formula Rule -> Property
prop_lRemoveShift p =
  forAll (arbitraryNodeAddrFor p) $ \a ->
    lIsLine a p && lIsLine (incrementNodeAddr a) p ==>
      lLookup a (lRemove a p) === lLookup (incrementNodeAddr a) p

lRemoveQCTests :: TestTree
lRemoveQCTests =
  testGroup
    "Testing lRemove"
    [ QC.testProperty "prop_lRemoveMinus1" prop_lRemoveMinus1,
      QC.testProperty "prop_lRemoveShift" prop_lRemoveShift
    ]

-- -- TESTING lInsert
prop_lInsertBeforeFormulaPlus1 :: Proof Formula Rule -> Property
prop_lInsertBeforeFormulaPlus1 (ProofLine {}) = discard
prop_lInsertBeforeFormulaPlus1 p@(SubProof {}) =
  forAll (arbitraryNodeAddrFor p) $ \a ->
    lIsFormula a p ==>
      lLength (lInsert (Left $ Formula 0) a Before p) === lLength p + 1

prop_lInsertAfterFormulaPlus1 :: Proof Formula Rule -> Property
prop_lInsertAfterFormulaPlus1 p =
  forAll (arbitraryNodeAddrFor p) $ \a ->
    lIsFormula a p ==>
      (lLength (lInsert (Left $ Formula 0) a After p) == lLength p + 1)

prop_lInsertlLookupFormulaBefore :: Proof Formula Rule -> Property
prop_lInsertlLookupFormulaBefore p =
  forAll (arbitraryNodeAddrFor p) $ \a ->
    lIsFormula a p ==>
      (lLookup a (lInsert (Left $ Formula 0) a Before p) == Just (Left $ Formula 0))

prop_lInsertlLookupFormulaAfter :: Proof Formula Rule -> Property
prop_lInsertlLookupFormulaAfter p =
  forAll (arbitraryNodeAddrFor p) $ \a ->
    lIsFormula a p ==>
      (lLookup (incrementNodeAddr a) (lInsert (Left $ Formula 0) a After p) == Just (Left $ Formula 0))

prop_lInsertBeforeLinePlus1 :: Proof Formula Rule -> Property
prop_lInsertBeforeLinePlus1 p =
  forAll (arbitraryNodeAddrFor p) $ \a ->
    lIsLine a p ==>
      (lLength (lInsert (Right $ Derivation (Formula 0) (Rule 0) []) a Before p) == lLength p + 1)

prop_lInsertAfterLinePlus1 :: Proof Formula Rule -> Property
prop_lInsertAfterLinePlus1 p =
  forAll (arbitraryNodeAddrFor p) $ \a ->
    lIsLine a p ==>
      (lLength (lInsert (Right $ Derivation (Formula 0) (Rule 0) []) a After p) == lLength p + 1)

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
prop_fromNodeAddrInverse p = forAll (arbitraryNodeAddrFor p) $ \a ->
  isJust (fromNodeAddr a p) ==>
    fromLineNo (fromJust $ fromNodeAddr a p) p === Just a

lineNoQCTests :: TestTree
lineNoQCTests =
  testGroup
    "testing conversion of lineNo and NodeAddr"
    [ QC.testProperty "prop_fromLineNoInverse" prop_fromLineNoInverse,
      QC.testProperty "prop_fromNodeAddrInverse" prop_fromNodeAddrInverse
    ]

proofTests :: TestTree
proofTests =
  testGroup
    "Testing functions concerning the modification of proofs"
    [ testGroup "QuickCheck" [lRemoveQCTests, lInsertQCTests, lineNoQCTests],
      testGroup "HUnit" []
    ]