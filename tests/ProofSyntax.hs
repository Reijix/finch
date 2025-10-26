module ProofSyntax where

import Control.Monad
import Data.Maybe (fromMaybe)
import Proof.Syntax
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC

--------------------------------------------
-- UNIT TESTS
derivation = Derivation Formula Rule []

line = ProofLine derivation

exProof :: Proof Formula Rule
exProof =
  SubProof
    [Formula, Formula]
    [ SubProof [Formula] [line] derivation
    ]
    derivation

exProof' :: Proof Formula Rule
exProof' =
  SubProof
    [Formula]
    [line, SubProof [Formula, Formula] [line, line] derivation]
    derivation

lRemoveEdge :: TestTree
lRemoveEdge = testCase "lRemoveEdge" $ lRemove 2 exProof' @?= Just exProof''
  where
    exProof'' =
      SubProof
        [Formula]
        [line, SubProof [Formula] [line, line] derivation]
        derivation

lRemoveTests01 :: [TestTree]
lRemoveTests01 =
  [ testCase "lRemove 0" $ lRemove 0 exProof @?= Just exProof',
    testCase "lRemove 1" $ lRemove 1 exProof @?= Just exProof'
  ]
  where
    exProof' =
      SubProof
        [Formula]
        [ SubProof [Formula] [ProofLine (Derivation Formula Rule [])] (Derivation Formula Rule [])
        ]
        (Derivation Formula Rule [])

lRemoveTestsNoRemove :: [TestTree]
lRemoveTestsNoRemove =
  [ testCase "lRemove 4" $ lRemove 4 exProof @?= Nothing,
    testCase "lRemove 5" $ lRemove 5 exProof @?= Nothing
  ]

lRemoveTest2 :: TestTree
lRemoveTest2 = testCase "lRemove 2" $ lRemove 2 exProof @?= Just exProof'
  where
    exProof' =
      SubProof
        [Formula, Formula]
        [ SubProof [] [ProofLine (Derivation Formula Rule [])] (Derivation Formula Rule [])
        ]
        (Derivation Formula Rule [])

lRemoveTest3 :: TestTree
lRemoveTest3 = testCase "lRemove 3" $ lRemove 3 exProof @?= Just exProof'
  where
    exProof' =
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
            l <- chooseInt (1, 3)
            vectorOf l (proof' (n `div` 2))

prop_lRemoveMinus1 :: Proof Formula Rule -> Property
prop_lRemoveMinus1 p = forAll (chooseInt (0, lLength p)) $ \n -> lIsMovable n p ==> maybe 0 lLength (lRemove n p) == lLength p - 1

lRemoveTests :: TestTree
lRemoveTests =
  testGroup
    "Testing lRemove"
    [ testGroup
        "QuickCheck"
        [QC.testProperty "prop_lRemoveMinus1" prop_lRemoveMinus1],
      testGroup
        "HUnit"
        (lRemoveEdge : lRemoveTest2 : lRemoveTest3 : lRemoveTests01 ++ lRemoveTestsNoRemove)
    ]