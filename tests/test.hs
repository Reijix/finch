import Data.List
import Data.Ord
import ProofSyntax
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Tests" [properties, unitTests]

properties :: TestTree
properties = testGroup "Properties" [lRemoveTests]

unitTests :: TestTree
unitTests =
  testGroup
    "Unit tests"
    []

-- unitTests :: TestTree
-- unitTests =
--   testGroup
--     "Unit tests"
--     [ testCase "List comparison (different length)" $
--         [1, 2, 3] `compare` [1, 2] @?= GT,
--       -- the following test does not hold
--       testCase "List comparison (same length)" $
--         [1, 2, 3] `compare` [1, 2, 2] @?= GT
--     ]