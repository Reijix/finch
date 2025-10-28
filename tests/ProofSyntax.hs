module ProofSyntax where

import Control.Monad
import Data.Maybe (fromMaybe)
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

lIsLineUnitTests :: TestTree
lIsLineUnitTests =
  testGroup
    "lIsLine"
    [testCase "lIsLine 2 exProof1" $ lIsLine 2 exProof1 @?= False]

lRemoveUnitTests :: TestTree
lRemoveUnitTests =
  testGroup
    "lRemove"
    [ testCase "lRemoveEdge2" $ lRemove 2 exProof2 @?= exProof2,
      testCase "lRemoveEdge" $ lRemove 2 exProof1 @?= exProof1',
      testCase "lRemove 0" $ lRemove 0 exProof0 @?= exProof0',
      testCase "lRemove 1" $ lRemove 1 exProof0 @?= exProof0'',
      testCase "lRemove 4" $ lRemove 4 exProof0 @?= exProof0,
      testCase "lRemove 5" $ lRemove 5 exProof0 @?= exProof0,
      testCase "lRemove 2" $ lRemove 2 exProof0 @?= exProof0''',
      testCase "lRemove 3" $ lRemove 3 exProof0 @?= exProof0''''
    ]
  where
    exProof1' =
      SubProof
        [Formula 0]
        [line 1, SubProof [Formula 3] [line 4, line 5] $ derivation 6]
        $ derivation 7
    exProof0' =
      SubProof
        [Formula 1]
        [ SubProof [Formula 2] [line 3] (derivation 4)
        ]
        (derivation 5)
    exProof0'' =
      SubProof
        [Formula 0]
        [ SubProof [Formula 2] [line 3] (derivation 4)
        ]
        (derivation 5)
    exProof0''' =
      SubProof
        [Formula 0, Formula 1]
        [ SubProof [] [line 3] (derivation 4)
        ]
        (derivation 5)
    exProof0'''' =
      SubProof
        [Formula 0, Formula 1]
        [ SubProof [Formula 2] [] (derivation 4)
        ]
        (derivation 5)

lInsertUnitTests :: TestTree
lInsertUnitTests =
  testGroup
    "lInsert"
    [ testCase "lInsert (Right $ derivation 0) 0 After exProof0" $ lInsert (Right $ derivation 0) 0 After exProof0 @?= exProof0,
      testCase "lInsert (Right $ derivation 0) 0 After exProof2" $ lInsert (Right $ derivation 0) 0 After exProof2 @?= exProof2'
    ]
  where
    exProof2' =
      SubProof
        []
        [ SubProof [] [line 0, line 0, line 1] $ derivation 2,
          SubProof
            [Formula 3, Formula 4]
            [line 5, line 6, line 7]
            (derivation 8)
        ]
        (derivation 9)

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

-- arbitrary :: Gen (Proof Formula Rule)
-- arbitrary = sized proof'
--   where
--     proof'' :: Int -> Gen (Proof Formula Rule)
--     proof'' 0 = fmap ProofLine arbitrary
--     proof'' n | n > 0 = oneof [fmap ProofLine arbitrary, liftM3 SubProof arbitrary ps arbitrary]
--       where
--         ps :: Gen [Proof Formula Rule]
--         ps = do
--           l <- chooseInt (1, 8)
--           vectorOf l (proof'' (n `div` 2))
--     -- Force outer proof to be a
--     proof' :: Int -> Gen (Proof Formula Rule)
--     proof' 0 = fmap ProofLine arbitrary
--     proof' n | n > 0 = liftM3 SubProof arbitrary ps arbitrary
--       where
--         ps :: Gen [Proof Formula Rule]
--         ps = do
--           l <- chooseInt (1, 8)
--           vectorOf l (proof'' (n `div` 2))

-- removing a movable line should decrement the length of the proof.
prop_lRemoveMinus1 :: Proof Formula Rule -> Property
prop_lRemoveMinus1 p =
  forAll (chooseInt (0, lLength p)) $ \n ->
    lIsMovable n p ==>
      lLength (lRemove n p) == lLength p - 1

-- removing a movable line should shift all indices by one.
prop_lRemoveShift :: Proof Formula Rule -> Property
prop_lRemoveShift p =
  forAll (chooseInt (0, lLength p)) $ \n ->
    (lIsMovable n p && lIsMovable (n + 1) p) ==>
      (lLookup (lRemove n p) n == lLookup p (n + 1))

lRemoveQCTests :: TestTree
lRemoveQCTests =
  testGroup
    "Testing lRemove"
    [ QC.testProperty "prop_lRemoveMinus1" prop_lRemoveMinus1,
      QC.testProperty "prop_lRemoveShift" prop_lRemoveShift
    ]

-- -- TESTING lInsert
prop_lInsertBeforeFormulaPlus1 :: Proof Formula Rule -> Property
prop_lInsertBeforeFormulaPlus1 p =
  forAll (chooseInt (0, lLength p)) $ \n ->
    lIsFormula n p ==>
      (lLength (lInsert (Left $ Formula 0) n Before p) == lLength p + 1)

prop_lInsertAfterFormulaPlus1 :: Proof Formula Rule -> Property
prop_lInsertAfterFormulaPlus1 p =
  forAll (chooseInt (0, lLength p)) $ \n ->
    lIsFormula n p ==>
      (lLength (lInsert (Left $ Formula 0) n After p) == lLength p + 1)

prop_lInsertlLookupFormulaBefore :: Proof Formula Rule -> Property
prop_lInsertlLookupFormulaBefore p =
  forAll (chooseInt (0, lLength p)) $ \n ->
    lIsFormula n p ==>
      (lLookup (lInsert (Left $ Formula 0) n Before p) n == Just (Left $ Formula 0))

prop_lInsertlLookupFormulaAfter :: Proof Formula Rule -> Property
prop_lInsertlLookupFormulaAfter p =
  forAll (chooseInt (0, lLength p)) $ \n ->
    lIsFormula n p ==>
      (lLookup (lInsert (Left $ Formula 0) n After p) (n + 1) == Just (Left $ Formula 0))

prop_lInsertBeforeLinePlus1 :: Proof Formula Rule -> Property
prop_lInsertBeforeLinePlus1 p =
  forAll (chooseInt (0, lLength p)) $ \n ->
    lIsLine n p ==>
      (lLength (lInsert (Right $ Derivation (Formula 0) (Rule 0) []) n Before p) == lLength p + 1)

prop_lInsertAfterLinePlus1 :: Proof Formula Rule -> Property
prop_lInsertAfterLinePlus1 p =
  forAll (chooseInt (0, lLength p)) $ \n ->
    lIsLine n p ==>
      (lLength (lInsert (Right $ Derivation (Formula 0) (Rule 0) []) n After p) == lLength p + 1)

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

proofTests :: TestTree
proofTests =
  testGroup
    "Testing functions concerning the modification of proofs"
    [ testGroup "QuickCheck" [lRemoveQCTests, lInsertQCTests],
      testGroup "HUnit" [lRemoveUnitTests, lInsertUnitTests, lIsLineUnitTests]
    ]