{- |
Module      : Fitch.Proof
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module defines data types for representing Fitch t'Proof's,
together with utilities for pretty-printing, indexing, querying, updating,
and reordering t'Proof's.
-}
module Fitch.Proof where

import Data.List (unsnoc)
import Data.Text qualified as T
import Relude.Extra.Map (toPairs, (!?))
import Relude.Extra.Newtype
import Util

------------------------------------------------------------------------------------------

-- * Pretty-printing

-- | Type class for pretty printing as t'Text'.
class PrettyPrint a where
  -- | Converts a value to its textual representation.
  prettyPrint :: a -> Text

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (a, b) where
  prettyPrint :: (PrettyPrint a, PrettyPrint b) => (a, b) -> Text
  prettyPrint (x, y) = "(" <> prettyPrint x <> "," <> prettyPrint y <> ")"

instance PrettyPrint Text where
  prettyPrint :: Text -> Text
  prettyPrint = id

instance (PrettyPrint a) => PrettyPrint [a] where
  prettyPrint :: [a] -> Text
  prettyPrint xs = unlines $ map prettyPrint xs

instance (PrettyPrint a) => PrettyPrint (NonEmpty a) where
  prettyPrint :: NonEmpty a -> Text
  prettyPrint (x :| xs) = prettyPrint (x : xs)

instance (PrettyPrint a, PrettyPrint b) => PrettyPrint (Either a b) where
  prettyPrint :: Either a b -> Text
  prettyPrint (Left x) = "Left " <> prettyPrint x
  prettyPrint (Right x) = "Right " <> prettyPrint x

instance (PrettyPrint a) => PrettyPrint (Maybe a) where
  prettyPrint :: Maybe a -> Text
  prettyPrint (Just x) = "Just " <> prettyPrint x
  prettyPrint Nothing = "Nothing"

instance (PrettyPrint a) => PrettyPrint (Map Name a) where
  prettyPrint :: Map Name a -> Text
  prettyPrint m = unlines $ map (\(n, a) -> n <> " |-> " <> prettyPrint a) (toPairs m)

------------------------------------------------------------------------------------------

-- * Parsed wrappers

-- | Wraps data with parsing and semantic information.
data Wrapper a where
  -- | Semantically valid parse success.
  ParsedValid :: Text -> a -> Wrapper a
  -- | Semantically invalid parse success.
  ParsedInvalid ::
    -- | User input.
    Text ->
    -- | Error message.
    Text ->
    -- | Inner value.
    a ->
    Wrapper a
  -- | Parse failure.
  Unparsed ::
    -- | User input.
    Text ->
    -- | Error message.
    Text ->
    Wrapper a
  deriving (Show, Eq)

instance PrettyPrint (Wrapper a) where
  prettyPrint :: Wrapper a -> Text
  prettyPrint = getText

-- | Returns whether a t'Wrapper' represents a parse failure.
isUnparsed :: Wrapper a -> Bool
isUnparsed (Unparsed{}) = True
isUnparsed _ = False

-- | Returns whether a t'Wrapper' represents a semantically valid parse.
isParseValid :: Wrapper a -> Bool
isParseValid (ParsedValid{}) = True
isParseValid _ = False

instance Functor Wrapper where
  fmap :: (a -> b) -> Wrapper a -> Wrapper b
  fmap f (ParsedValid txt x) = ParsedValid txt (f x)
  fmap f (ParsedInvalid txt err x) = ParsedInvalid txt err (f x)
  fmap _ (Unparsed txt err) = Unparsed txt err

-- | Extract data from a wrapper, returns v'Nothing' if no data is present.
fromWrapper :: Wrapper a -> Maybe a
fromWrapper (ParsedValid _ x) = Just x
fromWrapper (ParsedInvalid _ _ x) = Just x
fromWrapper (Unparsed{}) = Nothing

-- | Extract text value from a wrapper, always succeeds.
getText :: Wrapper a -> Text
getText (ParsedValid txt _) = txt
getText (ParsedInvalid txt _ _) = txt
getText (Unparsed txt _) = txt

------------------------------------------------------------------------------------------

-- | Renders a short preview of a t'Proof' as assumptions followed by its conclusion.
proofPreviewTex :: Proof -> Text
proofPreviewTex (SubProof fs _ (Derivation f _)) =
  T.concat viewFs
    <> "⊢\n"
    <> prettyPrint f
 where
  viewFs = map (\a -> prettyPrint a <> "\n") fs

------------------------------------------------------------------------------------------

-- * Proof Types

-- | Type of symbolic names such as variables, predicates, rules, and operators.
type Name = Text

{- | A term in first-order logics consists either of a variable or
a function applied to terms.
-}
data Term
  = -- | A single variable in first-order logic
    Var Name
  | -- | A function applied to terms in first-order logic
    Fun Name [Term]
  deriving (Eq, Ord, Show)

-- | Returns whether a t'Term' is a function application.
isFun :: Term -> Bool
isFun (Fun{}) = True
isFun _ = False

instance PrettyPrint Term where
  prettyPrint :: Term -> Text
  prettyPrint (Var v) = v
  prettyPrint (Fun f []) = f
  prettyPrint (Fun f ts) = f <> "(" <> T.intercalate "," (map prettyPrint ts) <> ")"

{- | A formula of first-order logic.
It can also represent propositional formulae by using v'Pred' without any t'Term's.
-}
data RawFormula
  = -- | A predicate applied to terms.
    Pred Name [Term]
  | -- | A predicate written in infix notation.
    InfixPred Name Term Term
  | -- | An n-ary operator, like @->@ for implication, or @~@ for negation.
    Opr Text [RawFormula]
  | -- | A quantifier, like @∀@ for universal quantification.
    Quantifier Name Name RawFormula
  deriving (Eq, Ord, Show)

instance PrettyPrint RawFormula where
  prettyPrint :: RawFormula -> Text
  prettyPrint f = go False f
   where
    go :: Bool -> RawFormula -> Text
    go _ (Pred p []) = p
    go _ (Pred p ts) = p <> "(" <> T.intercalate "," (map prettyPrint ts) <> ")"
    go _ (Opr op []) = op
    go _ (Opr op [f]) = op <> go True f
    go True f = "(" <> go False f <> ")"
    go False (InfixPred p t1 t2) = prettyPrint t1 <> " " <> p <> " " <> prettyPrint t2
    go False (Opr op [f1, f2]) = go True f1 <> " " <> op <> " " <> go True f2
    go False (Opr op fs) = op <> "(" <> T.intercalate "," (map prettyPrint fs) <> ")"
    go False (Quantifier q v f) = q <> v <> "." <> prettyPrint f

-- | A reference to either a single line or a whole subproof.
data Reference where
  -- | Referencing a single line.
  LineReference :: Int -> Reference
  -- | Referencing a subproof by its line range.
  ProofReference :: Int -> Int -> Reference
  deriving (Show, Eq)

instance PrettyPrint Reference where
  prettyPrint :: Reference -> Text
  prettyPrint (LineReference n) = show n
  prettyPrint (ProofReference start end) = show start <> "-" <> show end

-- | A formula with parsing and semantic information.
type Formula = Wrapper RawFormula

-- | The raw content of an t'Assumption'.
data RawAssumption
  = -- | A fresh variable of a t'Proof', written like @[c]@.
    FreshVar Name
  | -- | A regular t'RawFormula'.
    RawAssumption RawFormula
  deriving (Eq, Show)

{- | A wrapped assumption together with its attached t'RuleApplication'
for easily converting between t'Assumption' and t'Derivation'.
-}
type Assumption = (Wrapper RawAssumption, Wrapper RuleApplication)

-- | Constructs an t'Assumption' with the default rule @(⊤I)@.
mkAssumption :: Wrapper RawAssumption -> Assumption
mkAssumption w = (w, ParsedValid "(⊤I)" (RuleApplication "⊤I" []))

instance {-# OVERLAPPING #-} PrettyPrint Assumption where
  prettyPrint :: Assumption -> Text
  prettyPrint = prettyPrint . fst

{- | Converts a t'Derivation' into an t'Assumption' by wrapping its formula
as a t'RawAssumption'.
-}
toAssumption :: Derivation -> Assumption
toAssumption (Derivation (Unparsed txt err) ra) = (Unparsed txt err, ra)
toAssumption (Derivation (ParsedInvalid txt err f) ra) =
  (ParsedInvalid txt err (RawAssumption f), ra)
toAssumption (Derivation (ParsedValid txt f) ra) = (ParsedValid txt (RawAssumption f), ra)

{- | Converts an t'Assumption' into a t'Derivation'.
Fresh-variable assumptions cannot be converted to formulas and are therefore turned
into v'Unparsed'.
-}
toDerivation :: Assumption -> Derivation
toDerivation (Unparsed txt err, ra) = Derivation (Unparsed txt err) ra
toDerivation (ParsedInvalid txt err (RawAssumption f), ra) =
  Derivation (ParsedInvalid txt err f) ra
toDerivation (ParsedInvalid txt err a@(FreshVar v), ra) =
  Derivation (Unparsed (prettyPrint a) ("Could not parse " <> prettyPrint a)) ra
toDerivation (ParsedValid txt (RawAssumption f), ra) =
  Derivation (ParsedValid txt f) ra
toDerivation (ParsedValid txt a@(FreshVar v), ra) =
  Derivation (Unparsed (prettyPrint a) ("Could not parse " <> prettyPrint a)) ra

instance PrettyPrint RawAssumption where
  prettyPrint :: RawAssumption -> Text
  prettyPrint (RawAssumption f) = prettyPrint f
  prettyPrint (FreshVar v) = "[" <> v <> "]"

-- | Application of a rule.
data RuleApplication
  = -- | Application of a rule, consisting of the rule t'Name' and a list of t'Reference's.
    RuleApplication Name [Reference]
  deriving (Show, Eq)

instance {-# OVERLAPPING #-} PrettyPrint (Wrapper RuleApplication) where
  prettyPrint :: Wrapper RuleApplication -> Text
  prettyPrint (Unparsed "" _) = "()"
  prettyPrint w = getText w

instance PrettyPrint RuleApplication where
  prettyPrint :: RuleApplication -> Text
  prettyPrint (RuleApplication n refs) =
    "("
      <> n
      <> ")"
      <> " "
      <> T.intercalate "," (map prettyPrint refs)

-- | A derivation inside a t'Proof'.
data Derivation
  = {- | A single proof line consisting of a t'Formula'
    and the t'RuleApplication' that justifies it.
    -}
    Derivation Formula (Wrapper RuleApplication)
  deriving (Show, Eq)

instance PrettyPrint Derivation where
  prettyPrint :: Derivation -> Text
  prettyPrint (Derivation a ra) = prettyPrint a <> " " <> prettyPrint ra

-- | A datatype for representing Fitch-style proofs.
data Proof where
  {- | A sub proof consisting of t'Assumption's, t'Derivation's,
  nested t'Proof's, and a conclusion.
  -}
  SubProof :: [Assumption] -> [Either Derivation Proof] -> Derivation -> Proof
  deriving (Eq, Show)

instance PrettyPrint Proof where
  prettyPrint :: Proof -> Text
  prettyPrint p = pretty' 1 0 p
   where
    lineNoLen :: Int
    lineNoLen = T.length . show $ pLength p
    withLevel :: Int -> Text -> Text
    withLevel level t = T.replicate level "|" <> t <> "\n"
    withLine :: Int -> Text -> Text
    withLine line t = lineNo <> padding <> " " <> t
     where
      lineNo = show line
      padding = T.replicate (lineNoLen - T.length lineNo) " "
    withoutLine :: Text -> Text
    withoutLine = (T.replicate (lineNoLen + 1) " " <>)
    pretty' :: Int -> Int -> Proof -> Text
    pretty' line level (SubProof fs ps c) =
      T.concat fsShow
        <> withoutLine (withLevel (level + 1) "---")
        <> T.concat psShow
        <> cShow
     where
      (line', fsShow) =
        mapAccumL
          (\ln f -> (ln + 1, withLine ln $ withLevel (level + 1) $ prettyPrint f))
          line
          fs
      (line'', psShow) =
        mapAccumL
          ( \ln' e ->
              ( ln' + either (const 1) pLength e
              , either
                  (withLine ln' . withLevel (level + 1) . prettyPrint)
                  (pretty' ln' (level + 1))
                  e
              )
          )
          line'
          ps
      cShow = withLine line'' $ withLevel (level + 1) $ prettyPrint c

------------------------------------------------------------------------------------------

-- * Folds and Maps

{- | @'pFoldLines' af df s p@ folds the proof @p@ line-wise to a value
of type @a@ with starting value @s@.
-}
pFoldLines ::
  (a -> Assumption -> a) ->
  (a -> Derivation -> a) ->
  a ->
  Proof ->
  a
pFoldLines af df s (SubProof fs ps c) =
  df
    ( foldl'
        ( \s' ->
            either
              (df s')
              (pFoldLines af df s')
        )
        (foldl' af s fs)
        ps
    )
    c

-- | The 'pLength' of a t'Proof' is its total number of lines.
pLength :: Proof -> Int
pLength = pFoldLines (\n _ -> n + 1) (\n _ -> n + 1) 0

-- | Monadic variant of 'pFoldLines'.
pFoldLinesM ::
  (Monad m) =>
  (a -> Assumption -> m a) ->
  (a -> Derivation -> m a) ->
  a ->
  Proof ->
  m a
pFoldLinesM af df s (SubProof fs ps d) = do
  result1 <- foldlM af s fs
  result2 <- foldlM (\s' -> either (df s') (pFoldLinesM af df s')) result1 ps
  df result2 d

{- | Serializes a t'Proof' by mapping t'Assumption's, t'Derivation's, t'Proof's,
and conclusions.
Nested proofs are first serialized recursively
and then combined with the given proof function.
-}
pSerialize ::
  (Assumption -> a) ->
  (Derivation -> a) ->
  ([a] -> a) ->
  (Derivation -> a) ->
  Proof ->
  [a]
pSerialize af df pf cf (SubProof fs ps c) =
  map af fs
    <> map (either df (pf . pSerialize af df pf cf)) ps
    <> one (cf c)

{- | 'pSerializeLines' @af@ @df@ @p@ serializes the t'Proof' @p@ line-by-line,
applying @af@ to each t'Assumption' and @df@ to each t'Derivation',
and collecting the results into a flat list.
-}
pSerializeLines :: (Assumption -> a) -> (Derivation -> a) -> Proof -> [a]
pSerializeLines af df (SubProof fs ps d) =
  map af fs
    <> concatMap (either (one . df) (pSerializeLines af df)) ps
    <> one (df d)

{- | Like 'pSerializeLines' but also passes the current t'NodeAddr'
to each mapping function.
-}
pSerializeLinesWithAddr ::
  (NodeAddr -> Assumption -> a) ->
  (NodeAddr -> Derivation -> a) ->
  Proof ->
  [a]
pSerializeLinesWithAddr = go id
 where
  go ::
    (NodeAddr -> NodeAddr) ->
    (NodeAddr -> Assumption -> a) ->
    (NodeAddr -> Derivation -> a) ->
    Proof ->
    [a]
  go getNA af df (SubProof fs ps d) =
    mappedFs
      <> concat mappedPs
      <> [df (getNA NAConclusion) d]
   where
    (_, mappedFs) = mapAccumL (\m frm -> (m + 1, af (getNA $ NAAssumption m) frm)) 0 fs
    (_, mappedPs) =
      mapAccumL
        ( \m e ->
            ( m + 1
            , either
                (one . df (getNA (NALine m)))
                (go (getNA . NAProof m) af df)
                e
            )
        )
        0
        ps

{- | @'pMapLines' af df p@ maps each line of the t'Proof' @p@,
applying @af@ to every t'Assumption' and @df@ to every t'Derivation'.
-}
pMapLines ::
  (Assumption -> Assumption) ->
  (Derivation -> Derivation) ->
  Proof ->
  Proof
pMapLines af df (SubProof fs ps d) =
  SubProof
    (map af fs)
    (map (bimap df (pMapLines af df)) ps)
    (df d)

-- | Like 'pMapLines', but threads an accumulator from left to right.
pMapLinesAccumL ::
  (s -> Assumption -> (s, Assumption)) ->
  (s -> Derivation -> (s, Derivation)) ->
  s ->
  Proof ->
  (s, Proof)
pMapLinesAccumL af df s (SubProof fs ps d) =
  let
    (s', fs') = mapAccumL af s fs
    (s'', ps') =
      mapAccumL
        (\a e -> either (second Left . df a) (second Right . pMapLinesAccumL af df a) e)
        s'
        ps
    (s''', d') = df s'' d
   in
    (s''', SubProof fs' ps' d')

-- | Like 'pMapLines', but also passes the current line number to the mapping functions.
pMapLinesWithLineNo ::
  (Int -> Assumption -> Assumption) ->
  (Int -> Derivation -> Derivation) ->
  Proof ->
  Proof
pMapLinesWithLineNo af df = snd . pMapLinesAccumL af' df' 1
 where
  af' :: Int -> Assumption -> (Int, Assumption)
  af' n a = (n + 1, af n a)
  df' :: Int -> Derivation -> (Int, Derivation)
  df' n d = (n + 1, df n d)

-- | Like 'pMapLines', but also passes the current t'NodeAddr' to the mapping functions.
pMapLinesWithAddr ::
  (NodeAddr -> Assumption -> Assumption) ->
  (NodeAddr -> Derivation -> Derivation) ->
  Proof ->
  Proof
pMapLinesWithAddr = go id
 where
  go ::
    (NodeAddr -> NodeAddr) ->
    (NodeAddr -> Assumption -> Assumption) ->
    (NodeAddr -> Derivation -> Derivation) ->
    Proof ->
    Proof
  go getNA af df (SubProof fs ps d) = SubProof fs' ps' d'
   where
    (_, fs') = mapAccumL (\m frm -> (m + 1, af (getNA (NAAssumption m)) frm)) 0 fs
    (_, ps') =
      mapAccumL
        ( \m e ->
            ( m + 1
            , either
                (Left . df (getNA (NALine m)))
                (Right . go (getNA . NAProof m) af df)
                e
            )
        )
        0
        ps
    d' = df (getNA NAConclusion) d

-- | Like 'pMapLines' but lifted to monadic results.
pMapLinesM ::
  (Monad m) =>
  (Assumption -> m Assumption) ->
  (Derivation -> m Derivation) ->
  Proof ->
  m Proof
pMapLinesM af df (SubProof fs ps d) =
  liftA3
    SubProof
    (mapM af fs)
    (mapM (either ((Left <$>) . df) ((Right <$>) . pMapLinesM af df)) ps)
    (df d)

-- | Like 'pMapLinesM' but threads an accumulator from left to right.
pMapLinesMAccumL ::
  (Monad m) =>
  (s -> Assumption -> m (s, Assumption)) ->
  (s -> Derivation -> m (s, Derivation)) ->
  s ->
  Proof ->
  m (s, Proof)
pMapLinesMAccumL af df s (SubProof fs ps d) = do
  (s', fs') <-
    foldlM
      (\(t, fs') -> af t >=> (\(t', f') -> pure (t', fs' ++ [f'])))
      (s, [])
      fs
  (s'', ps') <-
    foldlM
      ( \(t, ps') ->
          either
            (df t >=> (\(t', d') -> pure (t', ps' <> [Left d'])))
            (pMapLinesMAccumL af df t >=> (\(t', p') -> pure (t', ps' <> [Right p'])))
      )
      (s', [])
      ps
  (s''', d') <- df s'' d
  pure (s''', SubProof fs' ps' d')

{- | Maps every t'Reference' in a t'Proof', optionally removing references
by returning 'Nothing'.
-}
pMapRefs :: (Reference -> Maybe Reference) -> Proof -> Proof
pMapRefs goRef = pMapLines goAssumption goDerivation
 where
  goAssumption :: Assumption -> Assumption
  goAssumption (a, r) = (a, goRule r)
  goDerivation :: Derivation -> Derivation
  goDerivation (Derivation f r) = Derivation f $ goRule r
  goRule :: Wrapper RuleApplication -> Wrapper RuleApplication
  goRule (Unparsed txt err) = Unparsed txt err
  goRule w@(ParsedInvalid txt err (RuleApplication name refs)) =
    let
      newRefs = mapMaybe goRef refs
      ra = RuleApplication name newRefs
     in
      if newRefs /= refs
        then ParsedInvalid (prettyPrint ra) err ra
        else w
  goRule w@(ParsedValid txt (RuleApplication name refs)) =
    let
      newRefs = mapMaybe goRef refs
      ra = RuleApplication name newRefs
     in
      if newRefs /= refs
        then ParsedValid (prettyPrint ra) ra
        else w

-- * Indexing proofs

{- | This type is used for indexing lines in a proof.
  Its recursive structure makes defining functions that manipulate proofs more convenient

A t'NodeAddr' may either be a reference to

* a single t'Assumption': v'NAAssumption' @n@,
* the conclusion: 'NAConclusion' of the t'Proof'
* the spot after the conclusion: 'NAAfterConclusion'
* a single t'Derivation' inside the proof @v'NALine' n@
* a reference to a nested element inside the t'Proof' 'NAProof' @n@ ('Just' @a@)
-}
data NodeAddr
  = -- | The @n@-th assumption of the current proof.
    NAAssumption Int
  | -- | The conclusion of the current proof.
    NAConclusion
  | -- | The position directly after the conclusion of the current proof.
    NAAfterConclusion
  | -- | The @n@-th derivation line of the current proof.
    NALine Int
  | -- | A nested address inside the @n@-th subproof of the current proof.
    NAProof Int NodeAddr
  deriving (Show, Eq)

instance Ord NodeAddr where
  compare :: NodeAddr -> NodeAddr -> Ordering
  compare (NAAssumption n) (NAAssumption m) = compare n m
  compare (NAAssumption _) (NALine _) = LT
  compare (NALine _) (NAAssumption _) = GT
  compare (NALine n) (NALine m) = compare n m
  compare (NALine n) (NAProof m _) = case compare n m of
    LT -> LT
    EQ -> LT
    GT -> GT
  compare (NAProof n _) (NALine m) = case compare n m of
    LT -> LT
    EQ -> GT
    GT -> GT
  compare (NAAssumption _) (NAProof _ _) = LT
  compare (NAProof _ _) (NAAssumption _) = GT
  compare (NAProof n addr1) (NAProof m addr2) | n == m = compare addr1 addr2
  compare (NAProof n _) (NAProof m _) = compare n m
  compare NAConclusion NAConclusion = EQ
  compare NAAfterConclusion NAAfterConclusion = EQ
  compare NAConclusion NAAfterConclusion = LT
  compare NAConclusion a = GT
  compare NAAfterConclusion a = GT
  compare a NAConclusion = LT
  compare a NAAfterConclusion = LT

-- | Returns whether a t'NodeAddr' points to an assumption of the current proof level.
isNAAssumption :: NodeAddr -> Bool
isNAAssumption NAAssumption{} = True
isNAAssumption _ = False

-- | Returns whether a t'NodeAddr' points to a possibly nested t'Assumption'.
isNestedNAAssumption :: NodeAddr -> Bool
isNestedNAAssumption (NAProof _ na) = isNestedNAAssumption na
isNestedNAAssumption NAAssumption{} = True
isNestedNAAssumption _ = False

-- | Returns whether a t'NodeAddr' points to a possibly nested t'Assumption'.
isNestedNAConclusion :: NodeAddr -> Bool
isNestedNAConclusion (NAProof _ na) = isNestedNAConclusion na
isNestedNAConclusion NAConclusion = True
isNestedNAConclusion _ = False

-- | Returns whether two t'NodeAddr's are on the same level in the same t'Proof'.
naInSameProof :: NodeAddr -> NodeAddr -> Bool
naInSameProof (NAProof n na1) (NAProof m na2) = n == m && naInSameProof na1 na2
naInSameProof
  (NAAssumption{}; NALine{}; NAConclusion; NAAfterConclusion)
  (NAAssumption{}; NALine{}; NAConclusion; NAAfterConclusion) = True
naInSameProof _ _ = False

-- | Returns whether two t'ProofAddr's are on the same level in the same t'Proof'.
paInSameProof :: ProofAddr -> ProofAddr -> Bool
paInSameProof (PANested n pa1) (PANested m pa2) = n == m && paInSameProof pa1 pa2
paInSameProof PAProof{} PAProof{} = True
paInSameProof _ _ = False

{- | Returns whether a t'NodeAddr' is the first line
in a t'Proof'. This could be because:

* it is the first assumption;
* there are no assumptions and it is the first line;
* there are no assumptions and it is the first line of the first subproof;
* there are no assumptions, no lines, no subproofs and it is the conclusion.
-}
isFirstLineIn :: Proof -> NodeAddr -> Bool
isFirstLineIn (SubProof (_ : _) _ _) (NAAssumption 0) = True
isFirstLineIn (SubProof [] (Left _ : _) _) (NALine 0) = True
isFirstLineIn (SubProof [] (Right p : _) _) (NAProof 0 na) = isFirstLineIn p na
isFirstLineIn (SubProof [] [] _) NAConclusion = True
isFirstLineIn _ _ = False

-- | Address of a t'Proof' within a t'Proof'.
data ProofAddr
  = -- | A nested t'Proof'.
    PANested Int ProofAddr
  | -- | The current t'Proof'.
    PAProof
  deriving (Show, Eq)

instance Ord ProofAddr where
  compare :: ProofAddr -> ProofAddr -> Ordering
  compare PAProof PAProof = EQ
  compare PAProof PANested{} = LT
  compare PANested{} PAProof = GT
  compare (PANested n1 pa1) (PANested n2 pa2) = case compare n1 n2 of
    LT -> LT
    EQ -> compare pa1 pa2
    GT -> GT

{- | Moves the given t'ProofAddr' one level higher,
returning a function that can be used to build t'ProofAddr's on the current level.
-}
paProofToNested :: ProofAddr -> (ProofAddr -> ProofAddr)
paProofToNested PAProof = id
paProofToNested (PANested n pa) = PANested n . paProofToNested pa

-- | Returns the t'ProofAddr' that contains the t'NodeAddr'.
paContaining :: NodeAddr -> ProofAddr
paContaining (NAAssumption{}; NALine{}; NAConclusion; NAAfterConclusion) = PAProof
paContaining (NAProof n na) = PANested n (paContaining na)

-- ** Conversion between line numbers and t'NodeAddr'

{- | Takes a line number and returns the corresponding t'NodeAddr' for a given t'Proof'.
Returns v'Nothing' on error.

__Note:__ t'NodeAddr' indices start at @0@, but line numbers start at @1@.
-}
fromLineNo ::
  Int ->
  Proof ->
  Maybe NodeAddr
fromLineNo n _ | n < 1 = Nothing
fromLineNo n (SubProof [] ps _) = helper n 0 ps
 where
  helper :: Int -> Int -> [Either Derivation Proof] -> Maybe NodeAddr
  helper 1 _ [] = Just NAConclusion
  helper n _ [] = Nothing
  helper 1 m (Left d : ps) = Just $ NALine m
  helper n m (Left d : ps) = helper (n - 1) (m + 1) ps
  helper n m (Right p : ps) | n - 1 < pLength p = do
    addr <- fromLineNo n p
    pure $ NAProof m addr
  helper n m (Right p : ps) = helper (n - pLength p) (m + 1) ps
fromLineNo n (SubProof fs _ _) | n - 1 < length fs = Just $ NAAssumption (n - 1)
fromLineNo n (SubProof fs ps l) = fromLineNo (n - length fs) (SubProof [] ps l)

{- | Takes a t'NodeAddr' and returns the corresponding line number for a given t'Proof'.

__Note:__ t'NodeAddr' indices start at @0@, but line numbers start at @1@.
-}
fromNodeAddr :: NodeAddr -> Proof -> Maybe Int
fromNodeAddr = go 1
 where
  go :: Int -> NodeAddr -> Proof -> Maybe Int
  go n (NAAssumption m) (SubProof fs _ _) | m < length fs = pure $ n + m
  go n (NAAssumption m) (SubProof fs _ _) = Nothing
  go 1 (NALine 0) (SubProof [] [] _) = Just 1
  go n (NALine m) (SubProof fs ps _)
    | holdsAt isLeft ps m =
        pure $
          length fs
            + n
            + foldr
              (\p n -> either (const $ n + 1) ((n +) . pLength) p)
              0
              (take m ps)
  go n NAConclusion (SubProof fs ps _) =
    pure $
      length fs
        + n
        + foldr
          (\p n -> either (const $ n + 1) ((n +) . pLength) p)
          0
          ps
  go n (NAProof m na) (SubProof fs ps@((!!? m) -> Just (Right p)) _) =
    go
      ( length fs
          + n
          + foldr
            (\p n -> either (const $ n + 1) ((n +) . pLength) p)
            0
            (take m ps)
      )
      na
      p
  go _ _ _ = Nothing

{- | Like 'fromNodeAddr',
but falls back to line number @999@ if the t'NodeAddr' is invalid.
-}
lineNoOr999 :: NodeAddr -> Proof -> Int
lineNoOr999 na p = fromMaybe 999 (fromNodeAddr na p)

{- | Returns the t'ProofAddr' of the t'Proof' spanning from the given start line
to the given end line, or v'Nothing' if no such t'Proof' exists.
-}
fromLineRange ::
  Int ->
  Int ->
  Proof ->
  Maybe ProofAddr
fromLineRange start end p = do
  -- get corresponding 'NodeAddr's
  lastLine <- fromLineNo end p

  -- Get 'ProofAddr' of the conclusion
  pa <-
    if isNestedNAConclusion lastLine
      then Just $ paContaining lastLine
      else Nothing

  -- compare starting line of pa with firstLine
  (start', _) <- lineRangeFromProofAddr pa p
  if start' == start
    then Just pa
    else Nothing

{- | Returns the start and end line numbers of the t'Proof' addressed by a t'ProofAddr'.
Returns v'Nothing' if the t'ProofAddr' is invalid.
-}
lineRangeFromProofAddr :: ProofAddr -> Proof -> Maybe (Int, Int)
lineRangeFromProofAddr PAProof p = Just (1, pLength p)
lineRangeFromProofAddr (PANested 0 pa) (SubProof fs (Right p : ps) _) =
  case lineRangeFromProofAddr pa p of
    Just (start, end) -> Just (start + length fs, end + length fs)
    Nothing -> Nothing
lineRangeFromProofAddr (PANested n pa) (SubProof fs (e : ps) c) | n > 0 =
  case lineRangeFromProofAddr (PANested (n - 1) pa) (SubProof fs ps c) of
    Just (start, end) ->
      Just
        ( start + either (const 1) pLength e
        , end
            + either
              (const 1)
              pLength
              e
        )
    Nothing -> Nothing
lineRangeFromProofAddr _ _ = Nothing

-- ** Utilities for working with addresses

{- | Increments a t'NodeAddr' index by 1, keeping the nesting structure unchanged.
Returns v'Nothing' for addresses without a numeric index (e.g. v'NAConclusion').
-}
incrementNodeAddr :: NodeAddr -> Maybe NodeAddr
incrementNodeAddr (NAAssumption n) = Just $ NAAssumption (n + 1)
incrementNodeAddr (NALine n) = Just $ NALine (n + 1)
incrementNodeAddr (NAProof n na) = NAProof n <$> incrementNodeAddr na
incrementNodeAddr _ = Nothing

{- | Converts a t'NodeAddr' to a t'ProofAddr', by

* Converting @v'NALine' n@ to @v'PAProof' n@
* Converting @v'NAConclusion n' to @v'PAProof' (length ps)@
* Converting @v'NAProof' n@ to @v'PANested' n@ and recursing.

For other t'NodeAddr's, returns v'Nothing'.
-}
paFromNA :: NodeAddr -> Proof -> Maybe ProofAddr
paFromNA (NALine n) _ = Just $ PANested n PAProof
paFromNA NAConclusion (SubProof _ ps _) = Just $ PANested (length ps) PAProof
paFromNA (NAProof n na) (SubProof _ ((!!? n) -> Just (Right p)) _) =
  PANested n
    <$> paFromNA na p
paFromNA _ _ = Nothing

{- | Turns a t'ProofAddr' into a function for building a t'NodeAddr'
that is contained in the t'ProofAddr'.
-}
naFromPA :: ProofAddr -> (NodeAddr -> NodeAddr)
naFromPA PAProof = id
naFromPA (PANested n pa) = NAProof n . naFromPA pa

-- | Returns a function that lifts a nested t'NodeAddr' by one proof level, if possible.
naLevelup2 :: NodeAddr -> Maybe (NodeAddr -> NodeAddr)
naLevelup2 = go id
 where
  go :: (NodeAddr -> NodeAddr) -> NodeAddr -> Maybe (NodeAddr -> NodeAddr)
  go na (NAProof _ NAConclusion) = Just na
  go na (NAProof _ NAAfterConclusion) = Just na
  go na (NAProof _ (NAAssumption _)) = Just na
  go na (NAProof _ (NALine _)) = Just na
  go na (NAProof m na') = go (na . NAProof m) na'
  go _ _ = Nothing

------------------------------------------------------------------------------------------

-- * Querying proofs

-- | Counts the number of parse or validation errors occurring in a t'Proof'.
proofErrors :: Proof -> Int
proofErrors (SubProof fs ps c) =
  foldr
    (\e n -> either derivationErrors proofErrors e + n)
    (foldr (\a n -> assumptionErrors a + n) 0 fs)
    ps
    + derivationErrors c
 where
  derivationErrors :: Derivation -> Int
  derivationErrors (Derivation f r)
    | isParseValid f && isParseValid r = 0
    | not (isParseValid f) && not (isParseValid r) = 2
    | otherwise = 1
  assumptionErrors :: Assumption -> Int
  assumptionErrors (f, _)
    | isParseValid f = 0
    | otherwise = 1

-- | Returns whether the element at the given index exists and satisfies a predicate.
holdsAt :: (a -> Bool) -> [a] -> Int -> Bool
holdsAt f xs n = maybe False f (xs !!? n)

{- | Returns whether the element at the given t'NodeAddr' exists
 and satisfies a predicate.
-}
holdsAtNA :: (Either Assumption Derivation -> Bool) -> Proof -> NodeAddr -> Bool
holdsAtNA f p na = maybe False f (naLookup na p)

{- | Returns whether the t'NodeAddr' is a valid address for the given t'Proof'.
(Valid in the sense that 'naLookup' would return a valid result.)
-}
naValid :: NodeAddr -> Proof -> Bool
naValid na p = isJust $ naLookup na p

{- | Returns the line at a given t'NodeAddr'.
Returns v'Nothing' if the t'NodeAddr' does not correspond to any line in the t'Proof'.
-}
naLookup :: NodeAddr -> Proof -> Maybe (Either Assumption Derivation)
naLookup (NAAssumption n) (SubProof fs _ _) = Left <$> fs !!? n
naLookup (NALine n) (SubProof _ ((!!? n) -> Just (Left d)) _) = Just . Right $ d
naLookup NAConclusion (SubProof _ _ c) = Just . Right $ c
naLookup (NAProof n na) (SubProof _ ((!!? n) -> Just (Right p)) _) = naLookup na p
naLookup _ _ = Nothing

-- | Returns the t'Proof' at a given t'ProofAddr' if it exists.
paLookup :: ProofAddr -> Proof -> Maybe Proof
paLookup (PANested n pa) (SubProof _ ((!!? n) -> Just (Right p)) _) = paLookup pa p
paLookup PAProof p = Just p
paLookup _ _ = Nothing

-- | Returns the t'Assumption' or t'Derivation' at the given line number if it exists.
pIndex :: Int -> Proof -> Maybe (Either Assumption Derivation)
pIndex n p = case fromLineNo n p of
  Nothing -> Nothing
  Just addr -> case naLookup addr p of
    Nothing -> Nothing
    Just (Left a) -> Just (Left a)
    Just (Right d) -> Just . Right $ d

-- | Returns the t'Proof' spanning the given start and end line numbers if it exists.
pIndexProof :: Int -> Int -> Proof -> Maybe Proof
pIndexProof start end p = fromLineRange start end p >>= (`paLookup` p)

{- | Returns whether the second t'NodeAddr' is relevant
when checking freshness for the first t'NodeAddr'.

I.e., whether the second t'NodeAddr' appears before the first one,
or appears on the same level.
-}
naAffectsFreshness :: NodeAddr -> NodeAddr -> Bool
naAffectsFreshness (NAProof n na1) (NAProof m na2)
  | n > m = True
  | n == m = naAffectsFreshness na1 na2
  | n < m = False
naAffectsFreshness
  (NAProof _ (NAAssumption{}; NALine{}; NAConclusion))
  (NAAssumption{}; NALine{}; NAConclusion) = True
naAffectsFreshness (NAProof{}) (NAAssumption{}) = False
naAffectsFreshness (NAProof n _) (NALine m) = m < n
naAffectsFreshness (NAProof{}) _ = False
naAffectsFreshness (NAAssumption n) (NAAssumption m) = m < n
naAffectsFreshness (NAAssumption _) (NALine{}; NAConclusion) = False
naAffectsFreshness _ _ = False

-- | Collects all lines relevant for freshness checking of the given t'NodeAddr'.
pCollectFreshnessNodes ::
  Proof -> NodeAddr -> [(NodeAddr, Either Assumption Derivation)]
pCollectFreshnessNodes p na =
  catMaybes $
    pSerializeLinesWithAddr
      (\na' a -> if naAffectsFreshness na na' then Just (na', Left a) else Nothing)
      (\na' d -> if naAffectsFreshness na na' then Just (na', Right d) else Nothing)
      p

-- * Updating proof contents

{- | 'naUpdateFormula' @f@ @addr@ @proof@ replaces the t'Assumption' or
t'Formula' at @addr@ in @proof@ using @f@.
Pass 'Left' to update an t'Assumption', or 'Right'
to update the t'Formula' of a t'Derivation'.
Returns v'Nothing' if the address does not exist or is incompatible
with the chosen update function.
-}
naUpdateFormula ::
  Either (Assumption -> Assumption) (Formula -> Formula) ->
  NodeAddr ->
  Proof ->
  Maybe Proof
naUpdateFormula (Left f) (NAAssumption n) (SubProof fs ps l) =
  liftA3
    SubProof
    (updateAtM n (pure . f) fs)
    (pure ps)
    (pure l)
naUpdateFormula (Right f) (NALine n) (SubProof fs ps l) =
  liftA3
    SubProof
    (pure fs)
    ( updateAtM
        n
        ( pure
            . either
              ( Left . \(Derivation formula rule) ->
                  Derivation (f formula) rule
              )
              Right
        )
        ps
    )
    (pure l)
naUpdateFormula (Right f) NAConclusion (SubProof fs ps (Derivation formula rule)) =
  Just $ SubProof fs ps (Derivation (f formula) rule)
naUpdateFormula f (NAProof n na) (SubProof fs ps l) =
  liftA3
    SubProof
    (pure fs)
    (updateAtM n (either (const Nothing) (fmap Right . naUpdateFormula f na)) ps)
    (pure l)
naUpdateFormula _ _ _ = Nothing

{- | 'naUpdateRule' @f@ @addr@ @proof@ updates the t'RuleApplication'
at @addr@ in @proof@ using @f@.
Returns v'Nothing' if the address does not exist
or points to an t'Assumption' (which has no editable t'RuleApplication').
-}
naUpdateRule ::
  (Wrapper RuleApplication -> Wrapper RuleApplication) ->
  NodeAddr ->
  Proof ->
  Maybe Proof
naUpdateRule f (NALine n) (SubProof fs ps l) =
  liftA3
    SubProof
    (pure fs)
    ( updateAtM
        n
        ( pure
            . either
              ( Left . \(Derivation formula rule) ->
                  Derivation formula (f rule)
              )
              Right
        )
        ps
    )
    (pure l)
naUpdateRule f NAConclusion (SubProof fs ps (Derivation formula rule)) =
  Just $ SubProof fs ps (Derivation formula (f rule))
naUpdateRule f (NAProof n na) (SubProof fs ps l) =
  liftA3
    SubProof
    (pure fs)
    (updateAtM n (either (const Nothing) (fmap Right . naUpdateRule f na)) ps)
    (pure l)
naUpdateRule _ _ p = Nothing

-- * (Re-)moving inside a proof

{- | @'naRemoveRaw' addr proof@ removes the element at a valid @addr@ from @proof@
without updating any t'Reference's.

For the v'NAConclusion' case: if the last element of @ps@ is a t'Derivation',
it is promoted to become the new conclusion. Otherwise v'Nothing' is returned.

__Note:__ Use 'naRemove' if references must stay consistent.
-}
naRemoveRaw :: NodeAddr -> Proof -> Maybe Proof
naRemoveRaw (NAAssumption n) (SubProof fs ps c) =
  liftA3
    SubProof
    (removeAt n fs)
    (pure ps)
    (pure c)
naRemoveRaw (NALine n) (SubProof fs ps c)
  | holdsAt isLeft ps n =
      liftA3
        SubProof
        (pure fs)
        (removeAt n ps)
        (pure c)
naRemoveRaw NAConclusion p@(SubProof fs ps c) = case unsnoc ps of
  Just (ps', Left d) -> Just $ SubProof fs ps' d
  _ -> Nothing
naRemoveRaw (NAProof n na) (SubProof fs ps c) =
  liftA3
    SubProof
    (pure fs)
    ( updateAtM
        n
        ( either
            (const Nothing)
            (fmap Right . naRemoveRaw na)
        )
        ps
    )
    (pure c)
naRemoveRaw _ _ = Nothing

{- | Removes the t'Proof' at a valid t'ProofAddr' without updating references.

__Note:__ Use 'paRemove' if references must stay consistent.
-}
paRemoveRaw :: ProofAddr -> Proof -> Maybe Proof
paRemoveRaw PAProof _ = Nothing
paRemoveRaw (PANested n PAProof) (SubProof fs ps c)
  | holdsAt isRight ps n =
      liftA3
        SubProof
        (pure fs)
        (removeAt n ps)
        (pure c)
  | otherwise = Nothing
paRemoveRaw (PANested n pa) (SubProof fs ps c) =
  liftA3
    SubProof
    (pure fs)
    (updateAtM n (either (const Nothing) (fmap Right . paRemoveRaw pa)) ps)
    (pure c)

-- | Removes the line at a valid t'NodeAddr' and updates all affected references.
naRemove :: NodeAddr -> Proof -> Maybe Proof
naRemove na (fromNodeAddr na -> Nothing) = Nothing
naRemove na p@(fromNodeAddr na -> Just lineNo) = pMapRefs goRef <$> naRemoveRaw na p
 where
  goRef :: Reference -> Maybe Reference
  goRef (LineReference line)
    | lineNo == line = Nothing
    | lineNo > line = Just $ LineReference line
    | lineNo < line = Just $ LineReference (line - 1)
  goRef (ProofReference start end)
    | lineNo < start = Just $ ProofReference (start - 1) (end - 1)
    | lineNo >= start && lineNo <= end = Just $ ProofReference start (end - 1)
    | lineNo >= start && lineNo > end = Just $ ProofReference start end

-- | Removes the t'Proof' at a valid t'ProofAddr' and updates all affected references.
paRemove :: ProofAddr -> Proof -> Maybe Proof
paRemove pa (lineRangeFromProofAddr pa -> Nothing) = Nothing
paRemove pa p@(lineRangeFromProofAddr pa -> Just (start, end)) =
  pMapRefs goRef
    <$> paRemoveRaw pa p
 where
  pLen = end - start + 1
  goRef :: Reference -> Maybe Reference
  goRef (LineReference line)
    | start <= line && line <= end = Nothing
    | start <= line && line > end = Just $ LineReference (line - pLen)
    | start > line = Just $ LineReference line
  goRef (ProofReference start' end')
    | start == start' = Nothing
    | start < start' = Just $ ProofReference (start' - pLen) (end' - pLen)
    | start > start' && start <= end' = Just $ ProofReference start' (end' - pLen)
    | start > start' && start > end' = Just $ ProofReference start' end'

{- | Inserts a line before the given t'NodeAddr' in the t'Proof',
without updating t'Reference's.

* 'naInsertBeforeRaw' ('Left' @a@) @addr@ @proof@
inserts the t'Assumption' @a@ before @addr@.
* 'naInsertBeforeRaw' ('Right' @d@) @addr@ @proof@
inserts the t'Derivation' @d@ before @addr@.

Returns the t'NodeAddr' of the inserted line together with the updated t'Proof'.
Returns v'Nothing' if line could not be inserted.

__Note:__ Use 'naInsertBefore' if references must stay consistent.
-}
naInsertBeforeRaw ::
  Either Assumption Derivation ->
  NodeAddr ->
  Proof ->
  Maybe (NodeAddr, Proof)
-- Inserting before NAAssumption
naInsertBeforeRaw (Left a) (NAAssumption n) (SubProof fs ps c) =
  fmap (NAAssumption n,) (liftA3 SubProof (insertAt a n fs) (pure ps) (pure c))
naInsertBeforeRaw (Right d) (NAAssumption n) (SubProof fs ps c) =
  fmap
    (NAAssumption n,)
    (liftA3 SubProof (insertAt (toAssumption d) n fs) (pure ps) (pure c))
-- Inserting before NALine
naInsertBeforeRaw (Left a) (NALine n) (SubProof fs ps c) =
  fmap
    (NALine n,)
    (liftA3 SubProof (pure fs) (insertAt (Left $ toDerivation a) n ps) (pure c))
naInsertBeforeRaw (Right d) (NALine n) (SubProof fs ps c) =
  fmap (NALine n,) (liftA3 SubProof (pure fs) (insertAt (Left d) n ps) (pure c))
-- Inserting before NAConclusion
naInsertBeforeRaw (Left a) NAConclusion (SubProof fs ps c) =
  pure (NALine (length ps), SubProof fs (ps <> one (Left $ toDerivation a)) c)
naInsertBeforeRaw (Right d) NAConclusion (SubProof fs ps c) =
  pure (NALine (length ps), SubProof fs (ps <> one (Left d)) c)
-- Inserting before NAAfterConclusion
naInsertBeforeRaw (Left a) NAAfterConclusion (SubProof fs ps c) =
  pure (NAConclusion, SubProof fs (ps <> one (Left c)) (toDerivation a))
naInsertBeforeRaw (Right d) NAAfterConclusion (SubProof fs ps c) =
  pure (NAConclusion, SubProof fs (ps <> one (Left c)) d)
-- Descent
naInsertBeforeRaw e (NAProof n na) (SubProof fs ps@((!!? n) -> Just (Right p)) c) =
  naInsertBeforeRaw e na p
    >>= \(addr, p') ->
      fmap
        (NAProof n addr,)
        ( liftA3
            SubProof
            (pure fs)
            (updateAtM n (either (const Nothing) (const . pure $ Right p')) ps)
            (pure c)
        )
naInsertBeforeRaw _ _ _ = Nothing

{- | Like 'naInsertBeforeRaw', but also updates references affected by the insertion.

Returns the t'NodeAddr' of the inserted line together with the updated t'Proof'.
-}
naInsertBefore ::
  Either Assumption Derivation ->
  NodeAddr ->
  Proof ->
  Maybe (NodeAddr, Proof)
naInsertBefore e na prf = case naInsertBeforeRaw e na prf of
  Just (na', p@(fromNodeAddr na' -> Just lineNo)) ->
    Just (na', pMapRefs (pure . goRef prf na' lineNo) p)
  _ -> Nothing
 where
  goRef :: Proof -> NodeAddr -> Int -> Reference -> Reference
  goRef p _ lineNo (LineReference line)
    | lineNo > line = LineReference line
    | lineNo <= line = LineReference $ line + 1
  goRef p na lineNo (ProofReference start end) = case fromLineRange start end p of
    Just pa
      | naContainedIn na pa -> ProofReference start (end + 1)
      | lineNo > end -> ProofReference start end
      | lineNo <= start -> ProofReference (start + 1) (end + 1)
    _ -> ProofReference start end

{- | Inserts a t'Proof' before the t'Proof' at the given t'ProofAddr'
without updating references.
Returns v'Nothing' if t'Proof' could not be inserted.

__Note:__ Use 'paInsertBefore' if references must stay consistent.
-}
paInsertBeforeRaw ::
  Proof ->
  ProofAddr ->
  Proof ->
  Maybe (ProofAddr, Proof)
paInsertBeforeRaw p (PANested n PAProof) (SubProof fs ps c) =
  fmap
    (PANested n PAProof,)
    ( liftA3
        SubProof
        (pure fs)
        (insertAt (Right p) n ps)
        (pure c)
    )
paInsertBeforeRaw p (PANested n pa) (SubProof fs ps@((!!? n) -> Just (Right prf)) c) =
  paInsertBeforeRaw p pa prf
    >>= \(pa, p') ->
      fmap
        (PANested n pa,)
        (liftA3 SubProof (pure fs) (updateAtM n (const . pure $ Right p') ps) (pure c))
paInsertBeforeRaw _ _ _ = Nothing

{- | Like 'paInsertBeforeRaw', but also updates references affected by the insertion.
Returns the t'ProofAddr' of the inserted t'Proof' together with the updated t'Proof'.
-}
paInsertBefore ::
  Proof ->
  ProofAddr ->
  Proof ->
  Maybe (ProofAddr, Proof)
paInsertBefore p pa prf = case paInsertBeforeRaw p pa prf of
  Just (pa, p@(lineRangeFromProofAddr pa -> Just (targetStart, targetEnd))) ->
    Just (pa, pMapRefs (pure . goRef prf pa (targetEnd - targetStart + 1) targetStart) p)
  _ -> Nothing
 where
  goRef :: Proof -> ProofAddr -> Int -> Int -> Reference -> Reference
  goRef _ _ offset lineNo (LineReference line)
    | lineNo > line = LineReference line
    | lineNo <= line = LineReference $ line + offset
  goRef p pa offset lineNo (ProofReference start end) = case fromLineRange start end p of
    Just pa'
      | lineNo > end -> ProofReference start end
      | paContainedIn pa pa' -> ProofReference start (end + offset)
      | lineNo <= start -> ProofReference (start + offset) (end + offset)
    _ -> ProofReference start end

{- | Moves the line at @source@ before the line at @target@ in t'Proof' @p@,
without updating any t'Reference's.
Returns the updated target t'NodeAddr' together with the modified t'Proof'
or v'Nothing' on failure.

__Note:__ Use 'naMoveBefore' if references must stay consistent.
-}
naMoveBeforeRaw :: NodeAddr -> NodeAddr -> Proof -> Maybe (NodeAddr, Proof)
naMoveBeforeRaw targetAddr sourceAddr p =
  if not (naCanMoveBefore p sourceAddr targetAddr)
    then Nothing
    else case (compare targetAddr sourceAddr, naLookup sourceAddr p) of
      (LT, Just node) -> do
        p' <- naRemoveRaw sourceAddr p
        naInsertBeforeRaw node targetAddr p'
      (GT, Just node) -> do
        -- since 'na' is fixed here already
        (na, p') <- naInsertBeforeRaw node targetAddr p
        p'' <- naRemoveRaw sourceAddr p'
        -- we might need to decrement 'na' by one, if sourceAddr is in the same proof.
        let
          naDecrementWhenOnSameLevel :: NodeAddr -> NodeAddr -> NodeAddr
          naDecrementWhenOnSameLevel (NAAssumption n) NAAssumption{}
            | n > 0 =
                NAAssumption (n - 1)
          naDecrementWhenOnSameLevel (NALine n) NALine{} | n > 0 = NALine (n - 1)
          naDecrementWhenOnSameLevel (NAProof n na) NALine{} | n > 0 = NAProof (n - 1) na
          naDecrementWhenOnSameLevel (NAProof n na1) (NAProof m na2)
            | n == m =
                NAProof n $ naDecrementWhenOnSameLevel na1 na2
          naDecrementWhenOnSameLevel na _ = na
        pure (naDecrementWhenOnSameLevel na sourceAddr, p'')
      _ -> Nothing

{- | Returns whether @lineNo@ falls within the given line range,
accounting for same-proof boundary rules.
-}
targetInRange :: Int -> (Int, Int) -> Proof -> Bool
targetInRange lineNo (start, end) p =
  lineNo > start && lineNo <= end
    || lineNo == start
      && maybe
        False
        (maybe (const False) naInSameProof (fromLineNo start p))
        (fromLineNo end p)

{- | Moves the line at @source@ before the line at @target@ in t'Proof' @p@,
and updates all t'Reference's affected by the move.
Returns v'Nothing' if the move is rejected by 'naCanMoveBefore'.
-}
naMoveBefore :: NodeAddr -> NodeAddr -> Proof -> Maybe (NodeAddr, Proof)
naMoveBefore targetAddr sourceAddr p =
  case naMoveBeforeRaw targetAddr sourceAddr p of
    Nothing -> Nothing
    Just (targetAddr', p') -> (targetAddr',) <$> go targetAddr' p'
 where
  go :: NodeAddr -> Proof -> Maybe Proof
  go targetAddr' p' =
    case (fromNodeAddr targetAddr' p', fromNodeAddr sourceAddr p) of
      (Just target, Just source) -> pure $ pMapRefs (pure . goRef target source) p'
      _ -> Nothing
  goRef :: Int -> Int -> Reference -> Reference
  goRef target source (LineReference line)
    | line == source = LineReference target
    | line < source && line >= target = LineReference (line + 1)
    | line > source && line <= target = LineReference (line - 1)
    | otherwise = LineReference line
  goRef target source (ProofReference start end) = case fromLineRange start end p of
    Nothing -> ProofReference start end
    Just pa
      | naContainedIn targetAddr pa && source < start -> ProofReference (start - 1) end
      | naContainedIn targetAddr pa && source > end -> ProofReference start (end + 1)
      | naContainedIn targetAddr pa -> ProofReference start end
      | target <= start && naContainedIn sourceAddr pa -> ProofReference (start + 1) end
      | target <= start && source > end -> ProofReference (start + 1) (end + 1)
      | target >= end && naContainedIn sourceAddr pa -> ProofReference start (end - 1)
      | target >= end && source < start -> ProofReference (start - 1) (end - 1)
      | otherwise -> ProofReference start end

{- | Returns whether a t'NodeAddr' is contained in the t'Proof'
designated by a t'ProofAddr'.

__Note:__ does not check if the t'NodeAddr' is valid!
-}
naContainedIn :: NodeAddr -> ProofAddr -> Bool
naContainedIn _ PAProof = True
naContainedIn (NAProof n na) (PANested m pa) = n == m && naContainedIn na pa
naContainedIn _ _ = False

{- | Returns whether a t'ProofAddr' is contained in another t'ProofAddr'.

__Note:__ does not check if either t'ProofAddr' is valid!
-}
paContainedIn :: ProofAddr -> ProofAddr -> Bool
paContainedIn PANested{} PAProof = True
paContainedIn (PANested n pa1) (PANested m pa2) = n == m && paContainedIn pa1 pa2
paContainedIn _ _ = False

-- | Returns whether the target address is identical to, or immediately after, the source.
naSameOrNext :: NodeAddr -> NodeAddr -> Proof -> Bool
naSameOrNext
  (NAProof n na)
  (NAProof ((== n) -> True) na')
  (SubProof _ ((!!? n) -> Just (Right p)) _) =
    naSameOrNext na na' p
naSameOrNext (NAAssumption n) (NAAssumption m) _ = n == m || n == m + 1
naSameOrNext (NALine n) (NALine m) _ = n == m || n == m + 1
naSameOrNext NAAfterConclusion NAConclusion _ = True
naSameOrNext NAConclusion NAConclusion _ = True
naSameOrNext NAConclusion (NALine n) (SubProof _ ps _) = n == length ps - 1
naSameOrNext _ _ _ = False

-- | Returns whether the target address is identical to, or immediately after, the source.
paSameOrNext :: ProofAddr -> ProofAddr -> Bool
paSameOrNext (PANested n PAProof) (PANested m PAProof) = n == m || n == m + 1
paSameOrNext (PANested n pa1) (PANested m pa2) | n == m = paSameOrNext pa1 pa2
paSameOrNext _ _ = False

{- | Helper for deciding whether a t'NodeAddr' may be moved to the target position
defaulting to v'True' and only does a real check for v'NAConclusion' where it
checks whether the conclusion has a t'Derivation' that can take its place, when it moves.
-}
naCanMoveConclusion :: NodeAddr -> Proof -> Bool
naCanMoveConclusion NAConclusion (SubProof fs ps c) = case unsnoc ps of
  Just (_, Left _) -> True
  _ -> False
naCanMoveConclusion (NAProof n na) (SubProof _ ((!!? n) -> Just (Right p)) _) =
  naCanMoveConclusion na p
naCanMoveConclusion _ _ = True

-- | Returns whether a t'NodeAddr' can be moved before the given target t'NodeAddr'.
naCanMoveBefore :: Proof -> NodeAddr -> NodeAddr -> Bool
naCanMoveBefore p source target =
  naCanMoveConclusion source p
    && not (naSameOrNext target source p)

-- | Returns whether a t'ProofAddr' can be moved before the given target t'ProofAddr'.
paCanMoveBefore :: ProofAddr -> ProofAddr -> Bool
paCanMoveBefore source target =
  not (paContainedIn target source)
    && not (paSameOrNext target source)

{- | Moves a t'Proof' before another t'Proof' without updating references.

__Note:__ Use 'paMoveBefore' if references must stay consistent.
-}
paMoveBeforeRaw :: ProofAddr -> ProofAddr -> Proof -> Maybe (ProofAddr, Proof)
paMoveBeforeRaw targetAddr sourceAddr p =
  if not (paCanMoveBefore sourceAddr targetAddr)
    then Nothing
    else case (compare targetAddr sourceAddr, paLookup sourceAddr p) of
      (LT, Just prf) -> do
        p' <- paRemoveRaw sourceAddr p
        paInsertBeforeRaw prf targetAddr p'
      (GT, Just prf) -> do
        (pa, p') <- paInsertBeforeRaw prf targetAddr p
        p'' <- paRemoveRaw sourceAddr p'
        let
          -- Decrements the new targetAddr by one, on the same level
          -- that sourceAddr lives.
          -- This is needed, because removal happens after insertion, so
          -- paInsertBeforeRaw returns a 'ProofAddr' that is not valid for p''.
          paDecrementWhenOnSameLevel :: ProofAddr -> ProofAddr -> ProofAddr
          paDecrementWhenOnSameLevel
            (PANested n pa)
            (PANested _ PAProof; PAProof) | n > 0 = PANested (n - 1) pa
          paDecrementWhenOnSameLevel pa@(PANested n pa1) (PANested m pa2)
            | n == m = PANested n $ paDecrementWhenOnSameLevel pa1 pa2
            | otherwise = pa
          paDecrementWhenOnSameLevel pa _ = pa
        pure (paDecrementWhenOnSameLevel pa sourceAddr, p'')
      _ -> Nothing

-- | Moves a t'Proof' before another t'Proof' and updates all affected references.
paMoveBefore :: ProofAddr -> ProofAddr -> Proof -> Maybe (ProofAddr, Proof)
paMoveBefore targetAddr sourceAddr p = case paMoveBeforeRaw targetAddr sourceAddr p of
  Nothing -> Nothing
  Just (targetAddr', p') -> (targetAddr',) <$> go targetAddr' p'
 where
  go :: ProofAddr -> Proof -> Maybe Proof
  go targetAddr' p' =
    case (lineRangeFromProofAddr targetAddr' p', lineRangeFromProofAddr sourceAddr p) of
      (Just targetRange, Just sourceRange) ->
        pure $ pMapRefs (pure . goRef targetRange sourceRange) p'
      _ -> Nothing
  goRef :: (Int, Int) -> (Int, Int) -> Reference -> Reference
  goRef (targetStart, targetEnd) (sourceStart, sourceEnd) (LineReference line)
    | inRange (sourceStart, sourceEnd) line = LineReference (targetStart + proofOffset)
    | line < sourceStart && targetStart <= line = LineReference (line + proofLen)
    | line > sourceEnd && targetEnd >= line = LineReference (line - proofLen)
    | otherwise = LineReference line
   where
    proofOffset = line - sourceStart
    proofLen = sourceEnd - sourceStart + 1
  goRef (targetStart, targetEnd) (sourceStart, sourceEnd) (ProofReference start end) =
    case fromLineRange start end p of
      Nothing -> ProofReference start end
      Just pa
        | start == sourceStart && end == sourceEnd ->
            ProofReference
              targetStart
              targetEnd
        | paContainedIn pa sourceAddr ->
            ProofReference
              (start + (targetStart - sourceStart))
              (end + (targetEnd - sourceEnd))
        | paContainedIn sourceAddr pa && not (paContainedIn targetAddr pa) ->
            case compare targetAddr pa of
              LT; EQ -> ProofReference (start + proofLen) end
              GT -> ProofReference start (end - proofLen)
        | paContainedIn targetAddr pa && not (paContainedIn sourceAddr pa) ->
            case compare sourceAddr pa of
              LT; EQ -> ProofReference (start - proofLen) end
              GT -> ProofReference start (end + proofLen)
        | not (paContainedIn targetAddr pa) && not (paContainedIn sourceAddr pa) ->
            case (compare sourceAddr pa, compare targetAddr pa) of
              ((,) (LT; EQ) GT) -> ProofReference (start - proofLen) (end - proofLen)
              ((,) GT (LT; EQ)) -> ProofReference (start + proofLen) (end + proofLen)
              _ -> ProofReference start end
        | otherwise -> ProofReference start end
   where
    proofLen = sourceEnd - sourceStart + 1
