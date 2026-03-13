{- |
Module      : Main
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (GHC extensions)

Entry point for testing. Runs the test suite using the
<https://hackage.haskell.org/package/tasty Tasty> framework.

QuickCheck is configured with:

* 'coverageReporter': shows code coverage.
* v'QuickCheckTests' @500@ — number of tests run per property.
* v'QuickCheckMaxRatio' @50@ — maximum ratio of discarded tests before a property is abandoned.
-}
module Main where

import FOLTest
import ProofSyntax
import Test.Tasty
import Test.Tasty.CoverageReporter
import Test.Tasty.QuickCheck

-- | Runs tests via Tasty
main :: IO ()
main =
  defaultMainWithIngredients (coverageReporter : defaultIngredients) $
    localOption (QuickCheckTests 500) $
      localOption (QuickCheckMaxRatio 50) $
        testGroup "Tests" [proofTests, verificationTests]
