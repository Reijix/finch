{- |
Module      : ProofSyntax
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (GHC extensions)

QuickCheck property tests for the t'Proof'
manipulation functions defined in "Fitch.Proof".

The module defines various helpers for constructing t'Proof's,
generators for arbitrarily generating t'Proof' and their contents as well as t'NodeAddr' and t'ProofAddr'.

Finally, this module defined properties concerning t'Proof', t'NodeAddr' and t'ProofAddr'.
-}
module ProofSyntax where

import Fitch.Proof
import Specification.Types
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck as QC
import Text.Show qualified

------------------------------------------------------------------------------------------

-- * Pretty Printing

-- | A wrapper around t'Proof' that replaces the derived 'Show' with 'PrettyPrint'.
newtype PrettyProof = PrettyProof Proof deriving (Eq)

-- | Unwraps a t'PrettyProof' back to the underlying t'Proof'.
fromPretty :: PrettyProof -> Proof
fromPretty (PrettyProof p) = p

-- | Pretty Printing via 'prettyPrint'.
instance Show PrettyProof where
  show :: PrettyProof -> String
  show (PrettyProof p) = toString $ prettyPrint p

-- * Constructing Proofs

-- This section introduces helpers for constructing t'Proof's with trivial data
-- where only the proof structure is relevant.

-- | Constructs a trivial t'Formula' consisting of an t'Int'.
formula :: Int -> Formula
formula n = ParsedValid (show n) $ Pred (show n) []

-- | Constructs a trivial t'Assumption' consisting of an t'Int'.
assumption :: Int -> Assumption
assumption n = mkAssumption $ ParsedValid (show n) $ RawAssumption $ Pred (show n) []

-- | Constructs a trivial t'RuleApplication' consisting of an t'Int'.
rule :: Int -> [Reference] -> Wrapper RuleApplication
rule n ref = ParsedValid (show n) (RuleApplication (show n) ref)

-- | Constructs a trivial t'Derivation' using 'formula' and 'rule'.
derivation :: Int -> Derivation
derivation n = Derivation (formula n) (rule n [])

------------------------------------------------------------------------------------------

-- Generators

-- | Generates a t'RuleApplication' based on 'rule'.
instance Arbitrary (Wrapper RuleApplication) where
  arbitrary :: Gen (Wrapper RuleApplication)
  arbitrary = liftA2 rule arbitrary (pure [])

-- | Generates an t'Assumption' based on 'assumption'.
instance {-# OVERLAPPING #-} Arbitrary Assumption where
  arbitrary :: Gen Assumption
  arbitrary = assumption <$> arbitrary

-- | Generates a t'Derivation' based on 'derivation'.
instance Arbitrary Derivation where
  arbitrary :: Gen Derivation
  arbitrary = derivation <$> arbitrary

{- | Generates an arbitrary t'Proof' using 'sized'.

* At size @0@: a v'SubProof' consisting only of a conclusion.
* At size @n > 0@: a v'SubProof' with arbitrary assumptions, between 1 and
  8 body lines (to prevent huge t'Proof's.), and an arbitrary
  conclusion.
-}
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

-- | Lifts 'Arbitrary' from t'Proof' to t'PrettyProof'.
instance Arbitrary PrettyProof where
  arbitrary :: Gen PrettyProof
  arbitrary = fmap PrettyProof arbitrary

------------------------------------------------------------------------------------------

-- * Address Generators

{- | Used for specifying which kind of t'NodeAddr's 'arbitraryNodeAddrFor' should
produce.
-}
data AddrKind = AddrKind
  { _assumptionKind :: Bool
  -- ^ a (possibly nested) 'NAAssumption'
  , _lineKind :: Bool
  -- ^ a (possibly nested) 'NALine'
  , _conclusionKind :: Bool
  -- ^  a (possibly nested) 'NAConclusion'
  , _afterConclusionKind :: Bool
  -- ^ a (possibly nested) 'NAAfterConclusion'
  }

-- | Empty t'AddrKind' with all fields set to v'False'
instance Monoid AddrKind where
  mempty =
    AddrKind
      { _assumptionKind = False
      , _lineKind = False
      , _conclusionKind = False
      , _afterConclusionKind = False
      }

-- | Combining t'AddrKind's, combines the fields with @||@.
instance Semigroup AddrKind where
  AddrKind ak1 lk1 ck1 ack1 <> AddrKind ak2 lk2 ck2 ack2 =
    AddrKind (ak1 || ak2) (lk1 || lk2) (ck1 || ck2) (ack1 || ack2)

-- | Constructor for setting '_assumptionKind'
assumptionKind :: AddrKind
assumptionKind = mempty{_assumptionKind = True}

-- | Constructor for setting '_lineKind'
lineKind :: AddrKind
lineKind = mempty{_lineKind = True}

-- | Constructor for setting '_conclusionKind'
conclusionKind :: AddrKind
conclusionKind = mempty{_conclusionKind = True}

-- | Constructor for setting '_afterConclusionKind'
afterConclusionKind :: AddrKind
afterConclusionKind = mempty{_afterConclusionKind = True}

-- | Constructor for setting all t'AddrKind's.
anyKind :: AddrKind
anyKind = assumptionKind <> lineKind <> conclusionKind <> afterConclusionKind

{- | Constructor for setting all t'AddrKind's that are __inside__ of the t'Proof',
i.e. excluding 'afterConclusionKind'.
-}
anyInsideKind :: AddrKind
anyInsideKind = assumptionKind <> lineKind <> conclusionKind

{- | Generates a valid t'NodeAddr' of the specified t'AddrKind'
for the given t'Proof'.
-}
arbitraryNodeAddrFor :: Proof -> AddrKind -> Gen NodeAddr
arbitraryNodeAddrFor (SubProof fs ps _) ak = do
  generators <- case catMaybes
    [ boolToMaybe naAssumption (fs /= [] && _assumptionKind ak)
    , boolToMaybe naLine (ps /= [] && _lineKind ak)
    , boolToMaybe naSubProof (ps /= [])
    , boolToMaybe (pure NAConclusion) (_conclusionKind ak)
    , boolToMaybe (pure NAAfterConclusion) (_afterConclusionKind ak)
    ] of
    [] -> discard
    l -> pure l
  oneof generators
 where
  boolToMaybe :: a -> Bool -> Maybe a
  boolToMaybe x True = Just x
  boolToMaybe _ False = Nothing
  naLine =
    maybe discard NALine <$> suchThatMaybe (chooseInt (0, length ps - 1)) (holdsAt isLeft ps)
  naAssumption = fmap NAAssumption (chooseInt (0, length fs - 1))
  naSubProof = do
    mn <- chooseInt (0, length ps - 1) `suchThatMaybe` holdsAt isRight ps
    case mn of
      Just n -> case ps !!? n of
        Just (Right p) -> arbitraryNodeAddrFor p ak <&> NAProof n
        _ -> discard
      _ -> discard

-- | Generates a valid t'ProofAddr' for the given t'Proof'.
arbitraryProofAddrFor :: Proof -> Gen ProofAddr
arbitraryProofAddrFor (SubProof fs ps c) = oneof [paProof, paNested]
 where
  paProof = pure PAProof
  paNested = do
    mn <- chooseInt (0, length ps - 1) `suchThatMaybe` holdsAt isRight ps
    case mn of
      Just n -> case ps !!? n of
        Just (Right p) -> arbitraryProofAddrFor p <&> PANested n
        _ -> discard
      _ -> discard

{- | Generates a valid @(start, end)@ line-number range within the given
t'Proof'.
-}
arbitraryLineRangeFor :: Proof -> Gen (Int, Int)
arbitraryLineRangeFor p@(SubProof _ ps _) = oneof [thisRange, nestedRange]
 where
  thisRange = pure (1, pLength p)
  nestedRange = do
    mn <- chooseInt (0, length ps - 1) `suchThatMaybe` holdsAt isRight ps
    case mn of
      Just n -> go n p
      Nothing -> discard
  go :: Int -> Proof -> Gen (Int, Int)
  go 0 (SubProof fs (Right p : ps) c) = do
    (start, end) <- arbitraryLineRangeFor p
    pure (start + length fs, end + length fs)
  go n (SubProof fs (e : ps) c) | n > 0 = do
    (start, end) <- go (n - 1) (SubProof fs ps c)
    pure (start + either (const 1) pLength e, end + either (const 1) pLength e)
  go _ _ = discard

------------------------------------------------------------------------------------------

-- * Properties: naRemove

{- | Removing a 'lineKind' or 'assumptionKind' decreases 'pLength' by exactly 1.

> pLength <$> naRemove a p  ===  Just (pLength p - 1)
-}
prop_naRemoveMinus1 :: PrettyProof -> Property
prop_naRemoveMinus1 (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p (assumptionKind <> lineKind)) $ \a ->
    (pLength <$> naRemove a p) === Just (pLength p - 1)

{- | After removing the t'Derivation' at address @a@, the entry that was immediately
after @a@ (at @'incrementNodeAddr' a@) is now reachable at address @a@.

> naLookup a <$> naRemove a p === Just ((`naLookup` p) =<< incrementNodeAddr a)
-}
prop_naRemoveShiftLine :: PrettyProof -> Property
prop_naRemoveShiftLine (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p lineKind) $ \a ->
    case holdsAtNA isRight p <$> incrementNodeAddr a of
      Nothing -> discard
      Just a' ->
        naLookup a <$> naRemove a p
      === Just ((`naLookup` p) =<< incrementNodeAddr a)

{- | After removing the t'Assumption' at address @a@, the entry that was immediately
after @a@ (at @'incrementNodeAddr' a@) is now reachable at address @a@.

> naLookup a <$> naRemove a p === Just ((`naLookup` p) =<< incrementNodeAddr a)
-}
prop_naRemoveShiftAssumption :: PrettyProof -> Property
prop_naRemoveShiftAssumption (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p assumptionKind) $ \a ->
    case holdsAtNA isLeft p <$> incrementNodeAddr a of
      Nothing -> discard
      Just a' ->
        naLookup a <$> naRemove a p
      === Just ((`naLookup` p) =<< incrementNodeAddr a)

------------------------------------------------------------------------------------------

-- * Properties: naInsertBefore

{- | A wrapper around 'naInsertBefore' that discards the
returned t'NodeAddr' and returns only the modified t'Proof'.
-}
naInsertBefore' ::
  Either Assumption Derivation ->
  NodeAddr ->
  Proof ->
  Maybe Proof
naInsertBefore' e na p = case naInsertBefore e na p of
  Just (_, p) -> Just p
  Nothing -> Nothing

{- | Inserting an t'Assumption' before an 'anyInsideKind' address increases
'pLength' by exactly 1.

> pLength <$> naInsertBefore' (Left (assumption 0)) a p  ===  Just (pLength p + 1)
-}
prop_naInsertBeforeAssumptionPlus1 :: PrettyProof -> Property
prop_naInsertBeforeAssumptionPlus1 (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p anyInsideKind) $ \a ->
    (pLength <$> naInsertBefore' (Left $ assumption 0) a p) === Just (pLength p + 1)

{- | Inserting a t'Derivation' before an 'anyInsideKind' address increases
'pLength' by exactly 1.

> pLength <$> naInsertBefore' (Right (derivation 0)) a p  ===  Just (pLength p + 1)
-}
prop_naInsertBeforeDerivationPlus1 :: PrettyProof -> Property
prop_naInsertBeforeDerivationPlus1 (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p lineKind) $ \a ->
    (pLength <$> naInsertBefore' (Right $ derivation 0) a p) === Just (pLength p + 1)

{- | After inserting @assumption 0@ before an 'assumptionKind' address,
'naLookup' returns @assumption 0@.


> naLookup a <$> naInsertBefore' (Left (assumption 0)) a p ===  Just (Just (Left (assumption 0)))
-}
prop_naInsertBeforeNaLookupAssumption :: PrettyProof -> Property
prop_naInsertBeforeNaLookupAssumption (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p assumptionKind) $ \na ->
    (naLookup na <$> naInsertBefore' (Left $ assumption 0) na p)
      === (Just . Just . Left $ assumption 0)

{- | After inserting @derivation 0@ before a 'lineKind' address,
'naLookup' returns @derivation 0@.

> naLookup a <$> naInsertBefore' (Right (derivation 0)) a p ===  Just (Just (Right (derivation 0)))
-}
prop_naInsertBeforeNaLookupDerivation :: PrettyProof -> Property
prop_naInsertBeforeNaLookupDerivation (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p lineKind) $ \na ->
    (naLookup na <$> naInsertBefore' (Right $ derivation 0) na p)
      === (Just . Just . Right $ derivation 0)

-- | Inserting an element and then removing it should return the original proof.
prop_naInsertBeforeRemove :: PrettyProof -> Property
prop_naInsertBeforeRemove (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p anyKind) $ \na ->
    (naInsertBefore (Right $ derivation 0) na p >>= uncurry naRemove)
      === Just p

------------------------------------------------------------------------------------------

-- * Properties: paMoveBefore

{- | Moving a t'Proof' to a new position with 'paMoveBeforeRaw' preserves
its content, i.e. looking up the source address in the original t'Proof' yields the
same t'Proof' as looking up the destination address in the modified t'Proof.

> paLookup paTarget' p'  ===  paLookup paSource p
-}
prop_paMoveBeforeRawSameProof :: PrettyProof -> Property
prop_paMoveBeforeRawSameProof (PrettyProof p) =
  forAll (arbitraryProofAddrFor p) $ \paSource ->
    forAll (arbitraryNodeAddrFor p lineKind) $ \naTarget -> case paFromNA naTarget p of
      Nothing -> discard
      Just paTarget ->
        if paTarget == paSource || paTarget == PAProof || paSource == PAProof
          then discard
          else case paMoveBeforeRaw paTarget paSource p of
            Nothing -> discard
            Just (paTarget', p') ->
              counterexample
                ( "paTarget="
                    <> show paTarget
                    <> "\npaTarget'="
                    <> show paTarget'
                    <> "\np'=\n"
                    <> toString (prettyPrint p')
                )
                $ (PrettyProof <$> paLookup paTarget' p') === (PrettyProof <$> paLookup paSource p)

------------------------------------------------------------------------------------------

-- * Properties: Line Number Conversion

{- | 'fromLineNo' followed by 'fromNodeAddr' is the identity on valid line
numbers.

> (fromNodeAddr addr p =<< fromLineNo n p)  ===  Just (Just n)
-}
prop_fromLineNoInverse :: PrettyProof -> Property
prop_fromLineNoInverse (PrettyProof p) = forAll (chooseInt (1, pLength p)) $ \n ->
  ((`fromNodeAddr` p) <$> fromLineNo n p)
    === Just (Just n)

{- | 'fromNodeAddr' followed by 'fromLineNo' is the identity on valid
t'NodeAddr' values.

> (fromLineNo n p =<< fromNodeAddr a p)  ===  Just (Just a)
-}
prop_fromNodeAddrInverse :: PrettyProof -> Property
prop_fromNodeAddrInverse (PrettyProof p) = forAll (arbitraryNodeAddrFor p anyInsideKind) $ \a ->
  ((`fromLineNo` p) <$> fromNodeAddr a p)
    === Just (Just a)

------------------------------------------------------------------------------------------

-- * Properties: Ordering on Addresses

{- | The 'Ord' instance for t'NodeAddr' is consistent with line-number
ordering: for any two addresses @a@ and @b@,

@
compare a b  ===  compare (fromNodeAddr a p) (fromNodeAddr b p)
@
-}
prop_compareLineNo :: PrettyProof -> Property
prop_compareLineNo (PrettyProof p) =
  forAll (arbitraryNodeAddrFor p anyInsideKind) $ \a ->
    forAll (arbitraryNodeAddrFor p anyInsideKind) $ \b ->
      compare a b
        === compare (fromNodeAddr a p) (fromNodeAddr b p)

------------------------------------------------------------------------------------------

-- * Properties: Line Range Conversion

{- | 'lineRangeFromProofAddr' followed by 'fromLineRange' is the identity
on valid t'ProofAddr' values.

> (fromLineRange s e p =<< lineRangeFromProofAddr pa p)  ===  Just pa
-}
prop_fromLineRangeInverse :: PrettyProof -> Property
prop_fromLineRangeInverse (PrettyProof p) = forAll (arbitraryProofAddrFor p) $ \pa ->
  ((\(s, e) -> fromLineRange s e p) =<< lineRangeFromProofAddr pa p) === Just pa

{- | 'fromLineRange' followed by 'lineRangeFromProofAddr' is the identity
on valid @(start, end)@ line ranges.

> (lineRangeFromProofAddr pa p =<< fromLineRange start end p) ===  Just (start, end)
-}
prop_lineRangeFromProofAddrInverse :: PrettyProof -> Property
prop_lineRangeFromProofAddrInverse (PrettyProof p) =
  forAll (arbitraryLineRangeFor p) $ \(start, end) ->
    ((`lineRangeFromProofAddr` p) =<< fromLineRange start end p) === Just (start, end)

------------------------------------------------------------------------------------------

-- * Tests

-- | Tests for 'naRemove'
naRemoveQCTests :: TestTree
naRemoveQCTests =
  testGroup
    "Testing naRemove"
    [ QC.testProperty "prop_naRemoveMinus1" prop_naRemoveMinus1
    , QC.testProperty "prop_naRemoveShiftLine" prop_naRemoveShiftLine
    , QC.testProperty "prop_naRemoveShiftAssumption" prop_naRemoveShiftAssumption
    ]

-- | Tests for 'naInsertBefore'
naInsertBeforeQCTests :: TestTree
naInsertBeforeQCTests =
  testGroup
    "Testing naInsertBefore"
    [ QC.testProperty "prop_naInsertBeforeFormulaPlus1" prop_naInsertBeforeAssumptionPlus1
    , QC.testProperty "prop_naInsertBeforeDerivationPlus1" prop_naInsertBeforeDerivationPlus1
    , QC.testProperty
        "prop_naInsertBeforeNaLookupAssumption"
        prop_naInsertBeforeNaLookupAssumption
    , QC.testProperty
        "prop_naInsertBeforeNaLookupDerivation"
        prop_naInsertBeforeNaLookupDerivation
    , QC.testProperty
        "prop_naInsertBeforeRemove"
        prop_naInsertBeforeRemove
    ]

-- | Tests for 'paMoveBefore'
paMoveBeforeQCTests :: TestTree
paMoveBeforeQCTests =
  testGroup
    "Testing paMoveBefore"
    [ QC.testProperty "prop_paMoveBeforeRawSameProof" prop_paMoveBeforeRawSameProof
    ]

-- | Tests regarding the conversion of line numbers and t'NodeAddr's.
lineNoQCTests :: TestTree
lineNoQCTests =
  testGroup
    "Testing conversion of line numbers and NodeAddr"
    [ QC.testProperty "prop_fromLineNoInverse" prop_fromLineNoInverse
    , QC.testProperty "prop_fromNodeAddrInverse" prop_fromNodeAddrInverse
    ]

-- | Tests for compare instances of address types like t'NodeAddr' and t'ProofAddr.
compareQCTests :: TestTree
compareQCTests =
  testGroup
    "Testing Ord instances"
    [ QC.testProperty "prop_compareLineNo" prop_compareLineNo
    ]

-- | Tests regarding the conversion of line ranges and t'ProofAddr's.
lineRangeQCTests :: TestTree
lineRangeQCTests =
  testGroup
    "Testing conversion of line ranges and ProofAddr"
    [ QC.testProperty "prop_fromLineRangeInverse" prop_fromLineRangeInverse
    , QC.testProperty "prop_lineRangeFromProofAddrInverse" prop_lineRangeFromProofAddrInverse
    ]

-- | Groups all tests in this module.
proofTests :: TestTree
proofTests =
  testGroup
    "QuickCheck tests for Fitch.Proof"
    [ naRemoveQCTests
    , naInsertBeforeQCTests
    , paMoveBeforeQCTests
    , lineNoQCTests
    , compareQCTests
    , lineRangeQCTests
    ]
