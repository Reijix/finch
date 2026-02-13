module ProofSyntax where

import Fitch.Proof
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Text.Show qualified

--------------------------------------------
-- UNIT TESTS

-- Definitions for unit testing:

newtype PrettyProof = PrettyProof Proof

fromPretty :: PrettyProof -> Proof
fromPretty (PrettyProof p) = p

instance Show PrettyProof where
  show :: PrettyProof -> String
  show (PrettyProof p) = toString $ prettyPrint p

formula :: Int -> Formula
formula n = ParsedValid (show n) $ Pred (show n) []

assumption :: Int -> Assumption
assumption n = ParsedValid (show n) $ RawAssumption $ Pred (show n) []

rule :: Int -> [Reference] -> Wrapper RuleApplication
rule n ref = ParsedValid (show n) (RuleApplication "Rule" ref)

derivation :: Int -> Derivation
derivation n = Derivation (formula n) (rule n [])

line :: Int -> Either Derivation Proof
line n = Left (derivation n)

-- example proof for removing a line
exProof0 :: PrettyProof
exProof0 =
  PrettyProof $
    SubProof
      [assumption 0, assumption 1]
      [ Right $ SubProof [assumption 2] [line 3] (derivation 4)
      ]
      (derivation 5)

-- example proof that triggered an edge case
exProof1 :: PrettyProof
exProof1 =
  PrettyProof $
    SubProof
      [assumption 0]
      [line 1, Right $ SubProof [assumption 2, assumption 3] [line 4, line 5] (derivation 6)]
      (derivation 7)

-- example proof that triggered another edge case
exProof2 :: PrettyProof
exProof2 =
  PrettyProof $
    SubProof
      []
      [ Right $ SubProof [] [line 0, line 1] $ derivation 2
      , Right $
          SubProof
            [assumption 3, assumption 4]
            [line 5, line 6, line 7]
            (derivation 8)
      ]
      (derivation 9)

exProof3 :: PrettyProof
exProof3 = PrettyProof $ SubProof [] [Right $ SubProof [assumption 0] [line 1] (derivation 2), line 3] (derivation 4)

--------------------------------------------
-- PROPERTIES
instance Arbitrary Name where
  arbitrary :: Gen Name
  arbitrary = pure "Rule"

instance Arbitrary RawFormula where
  arbitrary :: Gen RawFormula
  arbitrary = pure $ Pred "RawFormula" []

instance Arbitrary RawAssumption where
  arbitrary :: Gen RawAssumption
  arbitrary = RawAssumption <$> arbitrary

instance Arbitrary FormulaSpec where
  arbitrary :: Gen FormulaSpec
  arbitrary = pure $ FPred "RawFormula" []

instance Arbitrary RuleSpec where
  arbitrary :: Gen RuleSpec
  arbitrary = RuleSpec [] [] <$> arbitrary

instance Arbitrary RuleApplication where
  arbitrary :: Gen RuleApplication
  arbitrary = liftA2 RuleApplication arbitrary (pure [])

instance (Arbitrary a, PrettyPrint a) => Arbitrary (Wrapper a) where
  arbitrary :: Gen (Wrapper a)
  arbitrary = (arbitrary :: Gen a) >>= \a -> pure (ParsedValid (prettyPrint a) a)

instance Arbitrary Derivation where
  arbitrary :: Gen Derivation
  arbitrary = liftA2 Derivation arbitrary arbitrary

instance Arbitrary Proof where
  arbitrary :: Gen Proof
  arbitrary = sized proof'
   where
    proof' :: Int -> Gen Proof
    proof' 0 = liftA3 SubProof (pure []) (pure []) arbitrary
    proof' n | n > 0 = liftA3 SubProof arbitrary ps arbitrary
     where
      ps :: Gen [Either Derivation Proof]
      ps = do
        l <- chooseInt (1, 8)
        vectorOf l (resize (n `div` 2) arbitrary)

instance Arbitrary PrettyProof where
  arbitrary :: Gen PrettyProof
  arbitrary = fmap PrettyProof arbitrary

data AddrKind = AssumptionKind | LineKind | ProofKind | ConclusionKind | AnyKind

arbitraryNodeAddrFor :: Proof -> AddrKind -> Gen NodeAddr
arbitraryNodeAddrFor (SubProof fs ps l) ak = case (fs, ak) of
  ([], AssumptionKind) -> discard
  ([], AnyKind) -> oneof [naLine ps, naSubProof AnyKind, naConclusion]
  (_, AssumptionKind) -> oneof [naAssumption, naSubProof AssumptionKind]
  (_, LineKind) -> oneof [naLine ps, naSubProof LineKind]
  -- (_, ProofKind) -> oneof [naProof ps, naSubProof ProofKind]
  (_, ConclusionKind) -> oneof [naConclusion, naSubProof ConclusionKind]
  (_, AnyKind) -> oneof [naAssumption, naLine ps, naSubProof AnyKind, naConclusion]
 where
  naConclusion = pure NAConclusion
  naLine ps = maybe discard NALine <$> suchThatMaybe (chooseInt (0, length ps - 1)) (holdsAt isLeft ps)
  -- naProof ps = maybe discard (`NAProof` Nothing) <$> suchThatMaybe (chooseInt (0, length ps - 1)) (holdsAt isRight ps)
  naAssumption = fmap NAAssumption (chooseInt (0, length fs - 1))
  naSubProof ak = do
    mn <- chooseInt (0, length ps - 1) `suchThatMaybe` holdsAt isRight ps
    case mn of
      Just n -> case ps !!? n of
        Just (Right p) -> arbitraryNodeAddrFor p ak <&> NAProof n
        _ -> discard
      _ -> discard

prop_lRemoveMinus1 :: PrettyProof -> Property
prop_lRemoveMinus1 (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p LineKind) $ \a ->
    pLength (naRemove a p) === pLength p - 1

prop_lRemoveShift :: PrettyProof -> Property
prop_lRemoveShift (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p LineKind) $ \a ->
    case (`pIsLine` p) <$> incrementNodeAddr a of
      Nothing -> discard
      Just a' ->
        naLookup a (naRemove a p)
      === ((`naLookup` p) =<< incrementNodeAddr a)

lRemoveQCTests :: TestTree
lRemoveQCTests =
  testGroup
    "Testing naRemove"
    [ QC.testProperty "prop_lRemoveMinus1" prop_lRemoveMinus1
    , QC.testProperty "prop_lRemoveShift" prop_lRemoveShift
    ]

-- TESTING naInsertBefore
naInsertBefore' ::
  Either Assumption (Either Derivation Proof) ->
  NodeAddr ->
  Proof ->
  Maybe Proof
naInsertBefore' e na p = case naInsertBefore e na p of
  Just (_, p) -> Just p
  Nothing -> Nothing

prop_lInsertBeforeFormulaPlus1 :: PrettyProof -> Property
prop_lInsertBeforeFormulaPlus1 (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p AssumptionKind) $ \a ->
    (pLength <$> naInsertBefore' (Left $ assumption 0) a p) === Just (pLength p + 1)

prop_lInsertAfterFormulaPlus1 :: PrettyProof -> Property
prop_lInsertAfterFormulaPlus1 (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p AssumptionKind) $ \a ->
    (pLength <$> naInsertBefore' (Left $ assumption 0) a p) === Just (pLength p + 1)

prop_lInsertlLookupFormulaBefore :: PrettyProof -> Property
prop_lInsertlLookupFormulaBefore (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p AssumptionKind) $ \a ->
    (naLookup a <$> naInsertBefore' (Left $ assumption 0) a p) === (Just . Just . Left $ assumption 0)

prop_lInsertBeforeLinePlus1 :: PrettyProof -> Property
prop_lInsertBeforeLinePlus1 (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p LineKind) $ \a ->
    (pLength <$> naInsertBefore' (Right . Left $ derivation 0) a p) === Just (pLength p + 1)

prop_lInsertAfterLinePlus1 :: PrettyProof -> Property
prop_lInsertAfterLinePlus1 (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p LineKind) $ \a ->
    (pLength <$> naInsertBefore' (Right . Left $ derivation 0) a p) === Just (pLength p + 1)

lInsertQCTests :: TestTree
lInsertQCTests =
  testGroup
    "Testing naInsertBefore"
    [ QC.testProperty "prop_lInsertBeforeFormulaPlus1" prop_lInsertBeforeFormulaPlus1
    , QC.testProperty "prop_lInsertAfterFormulaPlus1" prop_lInsertAfterFormulaPlus1
    , QC.testProperty "prop_lInsertlLookupFormulaBefore" prop_lInsertlLookupFormulaBefore
    , QC.testProperty "prop_lInsertBeforeLinePlus1" prop_lInsertBeforeLinePlus1
    , QC.testProperty "prop_lInsertAfterLinePlus1" prop_lInsertAfterLinePlus1
    ]

prop_fromLineNoInverse :: PrettyProof -> Property
prop_fromLineNoInverse (PrettyProof p) = forAll (chooseInt (1, pLength p)) $ \n ->
  ((`fromNodeAddr` p) <$> fromLineNo n p)
    === Just (Just n)

prop_fromNodeAddrInverse :: PrettyProof -> Property
prop_fromNodeAddrInverse (PrettyProof p) = forAll (arbitraryNodeAddrFor p AnyKind) $ \a ->
  ((`fromLineNo` p) <$> fromNodeAddr a p)
    === Just (Just a)

lineNoQCTests :: TestTree
lineNoQCTests =
  testGroup
    "testing conversion of lineNo and NodeAddr"
    [ QC.testProperty "prop_fromLineNoInverse" prop_fromLineNoInverse
    , QC.testProperty "prop_fromNodeAddrInverse" prop_fromNodeAddrInverse
    ]

prop_compareLineNo :: PrettyProof -> Property
prop_compareLineNo (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p AnyKind) $ \a ->
    forAll (arbitraryNodeAddrFor p AnyKind) $ \b ->
      compare a b
        === compare (fromNodeAddr a p) (fromNodeAddr b p)

compareQCTests :: TestTree
compareQCTests =
  testGroup
    "testing compare instance of NodeAddr"
    [QC.testProperty "prop_compareLineNo" prop_compareLineNo]

-- TODO unit tests for pCollectFreshnessNodes
-- prop_collectVisibleLinesSmaller :: PrettyProof -> Property
-- prop_collectVisibleLinesSmaller (PrettyProof p) = forAll (arbitraryNodeAddrFor p AssumptionKind) $ \a ->
--   case pCollectVisibleLines a p of
--     Nothing -> False
--     Just nodes -> maybe False (length nodes <=) (fromNodeAddr a p)

-- collectVisibleLinesTests :: TestTree
-- collectVisibleLinesTests =
--   testGroup
--     "testing collectVisibleLines"
--     [QC.testProperty "prop_collectVisibleLinesSmaller" prop_collectVisibleLinesSmaller]

proofTests :: TestTree
proofTests =
  testGroup
    "Testing functions concerning the modification of proofs"
    [ testGroup "QuickCheck" [lRemoveQCTests, lInsertQCTests, lineNoQCTests, compareQCTests] -- ,collectVisibleLinesTests]
    , testGroup "HUnit" []
    ]