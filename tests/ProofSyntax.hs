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

arbitraryLineAddrFor :: Proof Formula Rule -> Gen LineAddr
arbitraryLineAddrFor (ProofLine {}) = return $ LADeriv 0 Nothing
arbitraryLineAddrFor (SubProof fs ps l) = case fs of
  [] -> laderiv
  _ -> oneof [laassumption, laderiv]
  where
    laassumption = fmap LAAssumption (chooseInt (0, L.length fs - 1))
    laderiv = do
      n <- chooseInt (0, L.length ps - 1)
      case ps !! n of
        ProofLine {} -> return $ LADeriv n Nothing
        p@(SubProof {}) -> arbitraryLineAddrFor p <&> (LADeriv n . Just)

prop_lRemoveAddrMinus1 :: Proof Formula Rule -> Property
prop_lRemoveAddrMinus1 (ProofLine {}) = discard
prop_lRemoveAddrMinus1 p@(SubProof {}) =
  forAll (arbitraryLineAddrFor p) $ \a ->
    lLength (lRemoveAddr a p) === lLength p - 1

prop_lRemoveAddrShift :: Proof Formula Rule -> Property
prop_lRemoveAddrShift p =
  forAll (arbitraryLineAddrFor p) $ \a ->
    lIsLineAddr a p && lIsLineAddr (incrementLineAddr a) p ==>
      lLookupAddr a (lRemoveAddr a p) === lLookupAddr (incrementLineAddr a) p

lRemoveQCTests :: TestTree
lRemoveQCTests =
  testGroup
    "Testing lRemove"
    [ QC.testProperty "prop_lRemoveAddrMinus1" prop_lRemoveAddrMinus1,
      QC.testProperty "prop_lRemoveAddrShift" prop_lRemoveAddrShift
    ]

-- -- TESTING lInsert
prop_lInsertBeforeFormulaPlus1 :: Proof Formula Rule -> Property
prop_lInsertBeforeFormulaPlus1 (ProofLine {}) = discard
prop_lInsertBeforeFormulaPlus1 p@(SubProof {}) =
  forAll (arbitraryLineAddrFor p) $ \a ->
    lIsFormulaAddr a p ==>
      lLength (lInsertAddr (Left $ Formula 0) a Before p) === lLength p + 1

prop_lInsertAfterFormulaPlus1 :: Proof Formula Rule -> Property
prop_lInsertAfterFormulaPlus1 p =
  forAll (arbitraryLineAddrFor p) $ \a ->
    lIsFormulaAddr a p ==>
      (lLength (lInsertAddr (Left $ Formula 0) a After p) == lLength p + 1)

prop_lInsertlLookupFormulaBefore :: Proof Formula Rule -> Property
prop_lInsertlLookupFormulaBefore p =
  forAll (arbitraryLineAddrFor p) $ \a ->
    lIsFormulaAddr a p ==>
      (lLookupAddr a (lInsertAddr (Left $ Formula 0) a Before p) == Just (Left $ Formula 0))

prop_lInsertlLookupFormulaAfter :: Proof Formula Rule -> Property
prop_lInsertlLookupFormulaAfter p =
  forAll (arbitraryLineAddrFor p) $ \a ->
    lIsFormulaAddr a p ==>
      (lLookupAddr (incrementLineAddr a) (lInsertAddr (Left $ Formula 0) a After p) == Just (Left $ Formula 0))

prop_lInsertBeforeLinePlus1 :: Proof Formula Rule -> Property
prop_lInsertBeforeLinePlus1 p =
  forAll (arbitraryLineAddrFor p) $ \a ->
    lIsLineAddr a p ==>
      (lLength (lInsertAddr (Right $ Derivation (Formula 0) (Rule 0) []) a Before p) == lLength p + 1)

prop_lInsertAfterLinePlus1 :: Proof Formula Rule -> Property
prop_lInsertAfterLinePlus1 p =
  forAll (arbitraryLineAddrFor p) $ \a ->
    lIsLineAddr a p ==>
      (lLength (lInsertAddr (Right $ Derivation (Formula 0) (Rule 0) []) a After p) == lLength p + 1)

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
    fromLineAddr (fromJust $ fromLineNo n p) p === Just n

prop_fromLineAddrInverse :: Proof Formula Rule -> Property
prop_fromLineAddrInverse p = forAll (arbitraryLineAddrFor p) $ \a ->
  fromLineNo (fromJust $ fromLineAddr a p) p === Just a

lineNoQCTests :: TestTree
lineNoQCTests =
  testGroup
    "testing conversion of lineNo and lineAddr"
    [ QC.testProperty "prop_fromLineNoInverse" prop_fromLineNoInverse,
      QC.testProperty "prop_fromLineAddrInverse" prop_fromLineAddrInverse
    ]

proofTests :: TestTree
proofTests =
  testGroup
    "Testing functions concerning the modification of proofs"
    [ testGroup "QuickCheck" [lRemoveQCTests, lInsertQCTests, lineNoQCTests],
      testGroup "HUnit" []
    ]