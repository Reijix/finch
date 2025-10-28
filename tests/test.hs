import Data.List
import Data.Ord
import ProofSyntax
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC

main :: IO ()
main = defaultMain $ localOption (QuickCheckTests 200) $ localOption (QuickCheckMaxRatio 50) tests

tests :: TestTree
tests = testGroup "Tests" [proofTests]