module ProofSyntax where

import Control.Monad
import Data.Maybe (fromMaybe)
import Proof.Syntax
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC

--------------------------------------------
-- UNIT TESTS
derivation :: Derivation Formula Rule
derivation = Derivation Formula Rule []

line :: Proof Formula Rule
line = ProofLine derivation

-- example proof for removing a line
exProof0 :: Proof Formula Rule
exProof0 =
  SubProof
    [Formula, Formula]
    [ SubProof [Formula] [line] derivation
    ]
    derivation

-- example proof that triggered an edge case
exProof1 :: Proof Formula Rule
exProof1 =
  SubProof
    [Formula]
    [line, SubProof [Formula, Formula] [line, line] derivation]
    derivation

-- example proof that triggered another edge case
exProof2 :: Proof Formula Rule
exProof2 =
  SubProof
    []
    [ SubProof [] [line, line] derivation,
      SubProof
        [Formula, Formula]
        [line, line, line]
        derivation
    ]
    derivation

lRemoveEdge2 :: TestTree
lRemoveEdge2 = testCase "lRemoveEdge2" $ lRemove 2 exProof2 @?= Nothing

-- remove line 2 from edge case (should remove the formula)
lRemoveEdge :: TestTree
lRemoveEdge = testCase "lRemoveEdge" $ lRemove 2 exProof1 @?= Just exProof1'
  where
    exProof1' =
      SubProof
        [Formula]
        [line, SubProof [Formula] [line, line] derivation]
        derivation

-- removing 0 or 1 should remove a formula
-- TODO adjust once Formula generator changed
lRemoveTests01 :: [TestTree]
lRemoveTests01 =
  [ testCase "lRemove 0" $ lRemove 0 exProof0 @?= Just exProof0',
    testCase "lRemove 1" $ lRemove 1 exProof0 @?= Just exProof0'
  ]
  where
    exProof0' =
      SubProof
        [Formula]
        [ SubProof [Formula] [ProofLine (Derivation Formula Rule [])] (Derivation Formula Rule [])
        ]
        (Derivation Formula Rule [])

-- removing 4 or 5 should change nothing
lRemoveTestsNoRemove :: [TestTree]
lRemoveTestsNoRemove =
  [ testCase "lRemove 4" $ lRemove 4 exProof0 @?= Nothing,
    testCase "lRemove 5" $ lRemove 5 exProof0 @?= Nothing
  ]

-- removing 2 should remove Formula
lRemoveTest2 :: TestTree
lRemoveTest2 = testCase "lRemove 2" $ lRemove 2 exProof0 @?= Just exProof0'
  where
    exProof0' =
      SubProof
        [Formula, Formula]
        [ SubProof [] [ProofLine (Derivation Formula Rule [])] (Derivation Formula Rule [])
        ]
        (Derivation Formula Rule [])

-- removing 3 should remove a proofline
lRemoveTest3 :: TestTree
lRemoveTest3 = testCase "lRemove 3" $ lRemove 3 exProof0 @?= Just exProof0'
  where
    exProof0' =
      SubProof
        [Formula, Formula]
        [ SubProof [Formula] [] (Derivation Formula Rule [])
        ]
        (Derivation Formula Rule [])

--------------------------------------------
-- PROPERTIES
data Formula = Formula deriving (Show, Eq)

data Rule = Rule deriving (Show, Eq)

instance Arbitrary Formula where
  arbitrary :: Gen Formula
  arbitrary = return Formula

instance Arbitrary (Derivation Formula Rule) where
  arbitrary :: Gen (Derivation Formula Rule)
  arbitrary = return $ Derivation Formula Rule []

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

-- removing a movable line should decrement the length of the proof.
prop_lRemoveMinus1 :: Proof Formula Rule -> Property
prop_lRemoveMinus1 p = forAll (chooseInt (0, lLength p)) $ \n -> lIsMovable n p ==> maybe 0 lLength (lRemove n p) == lLength p - 1

-- removing a movable line should shift all indices by one.
prop_lRemoveShift :: Proof Formula Rule -> Property
prop_lRemoveShift p = forAll (chooseInt (0, lLength p)) $ \n -> (lIsMovable n p && lIsMovable (n + 1) p) ==> maybe (Left Formula) (`lLookup` n) (lRemove n p) == lLookup p (n + 1)

lRemoveTests :: TestTree
lRemoveTests =
  testGroup
    "Testing lRemove"
    [ testGroup
        "QuickCheck"
        [ QC.testProperty "prop_lRemoveMinus1" prop_lRemoveMinus1,
          QC.testProperty "prop_lRemoveShift" prop_lRemoveShift
        ],
      testGroup
        "HUnit"
        (lRemoveEdge : lRemoveEdge2 : lRemoveTest2 : lRemoveTest3 : lRemoveTests01 ++ lRemoveTestsNoRemove)
    ]