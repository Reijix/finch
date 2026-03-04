module Fitch.Proof where

import Data.List (unsnoc)
import Data.Text qualified as T
import Relude.Extra.Map (toPairs, (!?))
import Relude.Extra.Newtype
import Util

-- * Definitions

class PrettyPrint a where
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

-- | Wraps data contained in a `Proof` to store further information.
data Wrapper a where
  -- | Semantically valid parse success
  ParsedValid :: Text -> a -> Wrapper a
  -- | Semantically invalid parse success
  ParsedInvalid ::
    -- | User input
    Text ->
    -- | Error message
    Text ->
    -- | Inner value
    a ->
    Wrapper a
  -- | Parse failure
  Unparsed :: Text -> Text -> Wrapper a
  deriving (Show, Eq)

instance PrettyPrint (Wrapper a) where
  prettyPrint :: Wrapper a -> Text
  prettyPrint = getText

isUnparsed :: Wrapper a -> Bool
isUnparsed (Unparsed{}) = True
isUnparsed _ = False

isParseValid :: Wrapper a -> Bool
isParseValid (ParsedValid{}) = True
isParseValid _ = False

instance Functor Wrapper where
  fmap :: (a -> b) -> Wrapper a -> Wrapper b
  fmap f (ParsedValid txt x) = ParsedValid txt (f x)
  fmap f (ParsedInvalid txt err x) = ParsedInvalid txt err (f x)
  fmap _ (Unparsed txt err) = Unparsed txt err

-- | Extract data from a wrapper, fails with an error if no data is present.
fromWrapper :: Wrapper a -> Maybe a
fromWrapper (ParsedValid _ x) = Just x
fromWrapper (ParsedInvalid _ _ x) = Just x
fromWrapper (Unparsed{}) = Nothing

-- | Extract text value from a wrapper.
getText :: Wrapper a -> Text
getText (ParsedValid txt _) = txt
getText (ParsedInvalid txt _ _) = txt
getText (Unparsed txt _) = txt

type ProofSpec = ([AssumptionSpec], FormulaSpec)

-- | The type of a fitch rule.
data RuleSpec
  = {- | A `RuleSpec` @assumptions@ @conclusion@ consists of
    a list of assumptions that are subproofs or formulae, and the conclusion.
    -}
    RuleSpec [FormulaSpec] [ProofSpec] FormulaSpec
  deriving (Show, Eq)

ruleSpecTex :: RuleSpec -> Text
ruleSpecTex (RuleSpec fs ps conclusion) =
  "\\frac{"
    <> showFsPs
    <> "}{"
    <> prettyPrint conclusion
    <> "}"
 where
  formulaSpecTex :: FormulaSpec -> Text
  formulaSpecTex = prettyPrint
  proofSpecTex :: ProofSpec -> Text
  proofSpecTex (as, f) =
    "\\begin{array}{|l}"
      <> showAs
      <> "\\\\ \\hline \\vdots \\\\ "
      <> prettyPrint f
      <> "\\end{array}"
   where
    showAs = T.intercalate "\\;" (map assumptionSpecTex as)
    assumptionSpecTex :: AssumptionSpec -> Text
    assumptionSpecTex (FFreshVar v) = "\\boxed{" <> v <> "}"
    assumptionSpecTex (AssumptionSpec frm) = formulaSpecTex frm
  showFsPs = T.intercalate "\\quad " (map formulaSpecTex fs <> map proofSpecTex ps)

proofPreviewTex :: Proof -> Text
proofPreviewTex (SubProof fs _ (Derivation f _)) = T.concat viewFs <> "⊢\n" <> prettyPrint f
 where
  viewFs = map (\a -> prettyPrint a <> "\n") fs

type Name = Text

-- | A term in first-order logics consists either of a variable or a function applied to terms.
data Term
  = -- | A single variable in first-order logic
    Var Name
  | -- | A function applied to terms in first-order logic
    Fun Name [Term]
  deriving (Eq, Ord, Show)

isFun :: Term -> Bool
isFun (Fun{}) = True
isFun _ = False

instance PrettyPrint Term where
  prettyPrint :: Term -> Text
  prettyPrint (Var v) = v
  prettyPrint (Fun f []) = f
  prettyPrint (Fun f ts) = f <> "(" <> T.intercalate "," (map prettyPrint ts) <> ")"

data Subst a = Subst Name a
  deriving (Show, Eq)

infixl 9 ~>
(~>) :: Name -> a -> Subst a
(~>) = Subst

data TermSpec
  = TVar Name
  | TFun Name [TermSpec]
  | TPlaceholder Name
  deriving (Eq, Show)

instance PrettyPrint TermSpec where
  prettyPrint :: TermSpec -> Text
  prettyPrint (TVar n) = n
  prettyPrint (TFun f ts) = f <> "(" <> T.intercalate "," (map prettyPrint ts) <> ")"
  prettyPrint (TPlaceholder n) = n

data FormulaSpec
  = FSubst Name (Subst Name)
  | FPlaceholder Name
  | FPred Name [TermSpec]
  | FInfixPredicate Name TermSpec TermSpec
  | FOpr Text [FormulaSpec]
  | FQuantifier Name Name FormulaSpec
  deriving (Eq, Show)

data AssumptionSpec
  = AssumptionSpec FormulaSpec
  | FFreshVar Name
  deriving (Eq, Show)

instance PrettyPrint FormulaSpec where
  prettyPrint :: FormulaSpec -> Text
  prettyPrint f = go False f
   where
    go :: Bool -> FormulaSpec -> Text
    go _ (FPred p []) = p
    go _ (FPred p ts) = p <> "(" <> T.intercalate "," (map prettyPrint ts) <> ")"
    go _ (FPlaceholder n) = n
    go _ (FSubst f (Subst n t)) = f <> "[" <> n <> " ↦ " <> t <> "]"
    go True f = "(" <> go False f <> ")"
    go False (FInfixPredicate p t1 t2) = prettyPrint t1 <> " " <> p <> " " <> prettyPrint t2
    go False (FOpr op []) = op
    go False (FOpr op [f]) = op <> go True f
    go False (FOpr op [f1, f2]) = go True f1 <> " " <> op <> " " <> go True f2
    go False (FOpr op fs) = op <> "(" <> T.intercalate "," (map prettyPrint fs) <> ")"
    go False (FQuantifier q v f) = q <> " " <> v <> ". " <> prettyPrint f

instance PrettyPrint AssumptionSpec where
  prettyPrint :: AssumptionSpec -> Text
  prettyPrint (AssumptionSpec fSpec) = prettyPrint fSpec
  prettyPrint (FFreshVar n) = "[" <> n <> "]"

-- | A formula for first-order logic (can be instantiated to 0th order, by using `Pred` without the list of `Term`.
data RawFormula
  = -- | A `Pred` applied to terms.
    Pred Name [Term]
  | -- | A `Pred` applied to terms, written in infix notation.
    InfixPredicate Name Term Term
  | -- | A n-ary operator, like @->@ for implication, or @~@ for negation.
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
    go True f = "(" <> go False f <> ")"
    go False (InfixPredicate p t1 t2) = prettyPrint t1 <> " " <> p <> " " <> prettyPrint t2
    go False (Opr op fs)
      | null fs = op
      | length fs == 2 = T.intercalate op (map (go True) fs)
      | otherwise = op <> "(" <> T.intercalate "," (map prettyPrint fs) <> ")"
    go False (Quantifier q v f) = q <> v <> "." <> prettyPrint f

-- go False (FreshVar v) = "[" <> v <> "]"

-- | A reference to a line (either `Formula` or `ProofLine` or a `SubProof`).
data Reference where
  -- | Referencing a single line
  LineReference :: Int -> Reference
  -- | Referencing a subproof by a line interval, i.e. `ProofReference` @from@ @to@
  ProofReference :: Int -> Int -> Reference
  deriving (Show, Eq)

instance PrettyPrint Reference where
  prettyPrint :: Reference -> Text
  prettyPrint (LineReference n) = show n
  prettyPrint (ProofReference start end) = show start <> "-" <> show end

-- | Assumptions are formulae wrapped with parsing and semantic information.
type Formula = Wrapper RawFormula

data RawAssumption
  = -- | A fresh variable of a subproof, written like @[c]@
    FreshVar Name
  | RawAssumption RawFormula
  deriving (Eq, Show)

type Assumption = (Wrapper RawAssumption, Wrapper RuleApplication)

mkAssumption :: Wrapper RawAssumption -> Assumption
mkAssumption w = (w, ParsedValid "(⊤I)" (RuleApplication "⊤I" []))

instance {-# OVERLAPPING #-} PrettyPrint Assumption where
  prettyPrint :: Assumption -> Text
  prettyPrint = prettyPrint . fst

toAssumption :: Derivation -> Assumption
toAssumption (Derivation (Unparsed txt err) ra) = (Unparsed txt err, ra)
toAssumption (Derivation (ParsedInvalid txt err f) ra) = (ParsedInvalid txt err (RawAssumption f), ra)
toAssumption (Derivation (ParsedValid txt f) ra) = (ParsedValid txt (RawAssumption f), ra)

toDerivation :: Assumption -> Derivation
toDerivation (Unparsed txt err, ra) = Derivation (Unparsed txt err) ra
toDerivation (ParsedInvalid txt err (RawAssumption f), ra) = Derivation (ParsedInvalid txt err f) ra
toDerivation (ParsedInvalid txt err a@(FreshVar v), ra) = Derivation (Unparsed (prettyPrint a) ("Could not parse " <> prettyPrint a)) ra
toDerivation (ParsedValid txt (RawAssumption f), ra) = Derivation (ParsedValid txt f) ra
toDerivation (ParsedValid txt a@(FreshVar v), ra) = Derivation (Unparsed (prettyPrint a) ("Could not parse " <> prettyPrint a)) ra

instance PrettyPrint RawAssumption where
  prettyPrint :: RawAssumption -> Text
  prettyPrint (RawAssumption f) = prettyPrint f
  prettyPrint (FreshVar v) = "[" <> v <> "]"

-- | Application of a rule
data RuleApplication
  = -- | Application of a rule, consisting of the `Name` of the rule, and a list of references.
    RuleApplication Name [Reference]
  deriving (Show, Eq)

instance {-# OVERLAPPING #-} PrettyPrint (Wrapper RuleApplication) where
  prettyPrint :: Wrapper RuleApplication -> Text
  prettyPrint (Unparsed "" _) = "()"
  prettyPrint w = getText w

instance PrettyPrint RuleApplication where
  prettyPrint :: RuleApplication -> Text
  prettyPrint (RuleApplication n refs) = "(" <> n <> ")" <> " " <> T.intercalate "," (map prettyPrint refs)

-- helper for debugging:
instance (PrettyPrint a) => PrettyPrint (Map Name a) where
  prettyPrint :: Map Name a -> Text
  prettyPrint m = unlines $ map (\(n, a) -> n <> " |-> " <> prettyPrint a) (toPairs m)

-- | A derivation inside a proof.
data Derivation
  = {- | A derivation inside a proof, i.e. a single line consisting of a formula
    and a ruleapplication that justifies how the formula was derived.
    -}
    Derivation Formula (Wrapper RuleApplication)
  deriving (Show, Eq)

instance PrettyPrint Derivation where
  prettyPrint :: Derivation -> Text
  prettyPrint (Derivation a ra) = prettyPrint a <> " " <> prettyPrint ra

-- | A datatype for respresenting fitch-style proofs.
data Proof where
  -- | A subproof consisting of a list of assumptions, a list of subproofs (or derivations) and a conclusion.
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
      (line', fsShow) = mapAccumL (\ln f -> (ln + 1, withLine ln $ withLevel (level + 1) $ prettyPrint f)) line fs
      (line'', psShow) =
        mapAccumL
          ( \ln' e ->
              ( ln' + either (const 1) pLength e
              , either (withLine ln' . withLevel (level + 1) . prettyPrint) (pretty' ln' (level + 1)) e
              )
          )
          line'
          ps
      cShow = withLine line'' $ withLevel (level + 1) $ prettyPrint c

-- | The `pLength` of a proof is its number of lines.
pLength :: Proof -> Int
pLength = pFoldLines (\n _ -> n + 1) (\n _ -> n + 1) 0

-- -- * Folding and mapping proofs

-- | `pFoldLines` @af@ @df@ @s@ @p@ folds the proof @p@, i.e. it reduces it line-wise to a value of type `a` with starting value @s@.
pFoldLines ::
  (a -> Assumption -> a) ->
  (a -> Derivation -> a) ->
  a ->
  Proof ->
  a
pFoldLines af df s (SubProof fs ps c) = df (foldl' (\s' -> either (df s') (pFoldLines af df s')) (foldl' af s fs) ps) c

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

-- | `pSerializeLines` @af@ @df@ @p@ serializes the proof @p@ by applying a function for each line in the proof and storing the results in a list.
pSerializeLines :: (Assumption -> a) -> (Derivation -> a) -> Proof -> [a]
pSerializeLines af df (SubProof fs ps d) =
  map af fs
    <> concatMap (either (one . df) (pSerializeLines af df)) ps
    <> one (df d)

-- | Like `pSerializeLines` but the current `NodeAddr` is dragged along.
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
  go getNA af df (SubProof fs ps d) = mappedFs ++ concat mappedPs ++ [df (getNA NAConclusion) d]
   where
    (_, mappedFs) = mapAccumL (\m frm -> (m + 1, af (getNA $ NAAssumption m) frm)) 0 fs
    (_, mappedPs) = mapAccumL (\m e -> (m + 1, either (one . df (getNA (NALine m))) (go (getNA . NAProof m) af df) e)) 0 ps

-- | `pMapLines` @af@ @df@ @p@ maps each line of the proof @p@ using functions @af@ and @df@.
pMapLines ::
  (Assumption -> Assumption) ->
  (Derivation -> Derivation) ->
  Proof ->
  Proof
pMapLines af df (SubProof fs ps d) = SubProof (map af fs) (map (bimap df (pMapLines af df)) ps) (df d)

pMapLinesAccumL ::
  (s -> Assumption -> (s, Assumption)) ->
  (s -> Derivation -> (s, Derivation)) ->
  s ->
  Proof ->
  (s, Proof)
pMapLinesAccumL af df s (SubProof fs ps d) =
  let
    (s', fs') = mapAccumL af s fs
    (s'', ps') = mapAccumL (\a e -> either (second Left . df a) (second Right . pMapLinesAccumL af df a) e) s' ps
    (s''', d') = df s'' d
   in
    (s''', SubProof fs' ps' d')

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
    (_, ps') = mapAccumL (\m e -> (m + 1, either (Left . df (getNA (NALine m))) (Right . go (getNA . NAProof m) af df) e)) 0 ps
    d' = df (getNA NAConclusion) d

-- | Like `pMapLines` but lifted to monadic results.
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

-- | Like `pMapLinesM` but an accumulator is dragged along.
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

==== Usage

A `NodeAddr` may either be a reference to

* a single assumption `NAAssumption` @n@,

* the conclusion `NAConclusion` of the proof

* a single proof or line inside the proof `NAProof` @n@ `Nothing`

* a reference to a nested element inside a subproof `NAProof` @n@ (`Just` @a@)
-}
data NodeAddr
  = NAAssumption Int
  | NAConclusion
  | NAAfterConclusion
  | NALine Int
  | NAProof Int NodeAddr
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

isNAAssumption :: NodeAddr -> Bool
isNAAssumption NAAssumption{} = True
isNAAssumption _ = False

isNestedNAAssumption :: NodeAddr -> Bool
isNestedNAAssumption (NAProof _ na) = isNestedNAAssumption na
isNestedNAAssumption NAAssumption{} = True
isNestedNAAssumption _ = False

naInSameProof :: NodeAddr -> NodeAddr -> Bool
naInSameProof (NAProof n na1) (NAProof m na2) = n == m && naInSameProof na1 na2
naInSameProof (NAAssumption{}; NALine{}; NAConclusion; NAAfterConclusion) (NAAssumption{}; NALine{}; NAConclusion; NAAfterConclusion) = True
naInSameProof _ _ = False

paInSameProof :: ProofAddr -> ProofAddr -> Bool
paInSameProof (PANested n pa1) (PANested m pa2) = n == m && paInSameProof pa1 pa2
paInSameProof PAProof{} PAProof{} = True
paInSameProof _ _ = False

-- TODO comment
data ProofAddr
  = PAProof Int
  | PANested Int ProofAddr
  deriving (Show, Eq)

instance Ord ProofAddr where
  compare :: ProofAddr -> ProofAddr -> Ordering
  compare (PAProof n) (PAProof m) = compare n m
  compare (PAProof n) (PANested m _) = case compare n m of
    LT -> LT
    EQ -> LT
    GT -> GT
  compare (PANested n _) (PAProof m) = case compare n m of
    LT -> LT
    EQ -> GT
    GT -> GT
  compare (PANested n addr1) (PANested m addr2) | n == m = compare addr1 addr2
  compare (PANested n _) (PANested m _) = compare n m

paProofToNested :: ProofAddr -> (ProofAddr -> ProofAddr)
paProofToNested (PAProof n) = PANested n
paProofToNested (PANested n pa) = PANested n . paProofToNested pa

-- ** Conversion between line numbers and `NodeAddr`

{- | Takes a line index and returns the corresponding `NodeAddr` for a given proof.

NOTE: indices of NodeAddr start at 0, but line numbers start at 1!
-}
fromLineNo :: Int -> Proof -> Maybe NodeAddr
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

fromLineRange :: Int -> Int -> Proof -> Maybe ProofAddr
fromLineRange start end p = join $ go start end 0 p
 where
  go :: Int -> Int -> Int -> Proof -> Maybe (Maybe ProofAddr)
  go start end _ _ | start < 1 || end < start = Nothing
  go 1 end n p = do
    first <- fromLineNo 1 p
    last <- fromLineNo end p
    unifyNAs first last p
   where
    unifyNAs :: NodeAddr -> NodeAddr -> Proof -> Maybe (Maybe ProofAddr)
    unifyNAs na NAConclusion p | isFirstLineIn p na = Just Nothing
     where
      isFirstLineIn :: Proof -> NodeAddr -> Bool
      isFirstLineIn (SubProof (_ : _) _ _) (NAAssumption 0) = True
      isFirstLineIn (SubProof [] (Left _ : _) _) (NALine 0) = True
      isFirstLineIn (SubProof [] (Right p : _) _) (NAProof 0 na) = isFirstLineIn p na
      isFirstLineIn (SubProof [] [] _) NAConclusion = True
      isFirstLineIn _ _ = False
    unifyNAs (NAProof n na1) (NAProof m na2) (SubProof _ ((!!? n) -> Just (Right p)) _) | n == m = case unifyNAs na1 na2 p of
      Nothing -> Nothing
      Just Nothing -> Just $ Just $ PAProof n
      Just (Just pa) -> Just $ Just $ PANested n pa
    unifyNAs _ _ _ = Nothing
  go start end n (SubProof fs (Left d : ps) c) = go (start - 1) (end - 1) (n + 1) (SubProof fs ps c)
  go start end n (SubProof fs (Right p : ps) c)
    | pLength p + length fs < start = go (start - pLength p) (end - pLength p) (n + 1) (SubProof fs ps c)
    | otherwise = case go (start - length fs) (end - length fs) 0 p of
        Nothing -> Nothing
        Just Nothing -> Just $ Just $ PAProof n
        Just (Just pa) -> Just $ Just $ PANested n pa
  go start end n p = Nothing

{- | Takes a `NodeAddr` and returns the corresponding line index for a given proof.

NOTE: indices of NodeAddr start at 0, but line numbers start at 1!
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
        pure $ length fs + n + foldr (\p n -> either (const $ n + 1) ((n +) . pLength) p) 0 (take m ps)
  go n NAConclusion (SubProof fs ps _) = pure $ length fs + n + foldr (\p n -> either (const $ n + 1) ((n +) . pLength) p) 0 ps
  go n (NAProof m na) (SubProof fs ps@((!!? m) -> Just (Right p)) _) = go (length fs + n + foldr (\p n -> either (const $ n + 1) ((n +) . pLength) p) 0 (take m ps)) na p
  go _ _ _ = Nothing

lineNoOr999 :: NodeAddr -> Proof -> Int
lineNoOr999 na p = fromMaybe 999 (fromNodeAddr na p)

lineRangeFromProofAddr :: ProofAddr -> Proof -> Maybe (Int, Int)
lineRangeFromProofAddr pa p = go 1 pa p
 where
  go :: Int -> ProofAddr -> Proof -> Maybe (Int, Int)
  go n (PAProof 0) (SubProof [] (e : _) c) = case e of
    Right p -> Just (n, n + pLength p - 1)
    _ -> Nothing
  go n (PAProof m) (SubProof [] (p : ps) c) = go (n + either (const 1) pLength p) (PAProof (m - 1)) (SubProof [] ps c)
  go n (PANested 0 pa) (SubProof [] (e : _) _) = case e of
    Right p -> go n pa p
    _ -> Nothing
  go n (PANested m pa) (SubProof [] (p : ps) c) = go (n + either (const 1) pLength p) (PANested (m - 1) pa) (SubProof [] ps c)
  go n pa (SubProof (f : fs) ps c) = go (n + length fs + 1) pa (SubProof [] ps c)
  go _ _ _ = Nothing

-- ** Utilities for working with addresses

-- | `incrementNodeAddr` increments an address by 1, while keeping the nesting structure unchanged.
incrementNodeAddr :: NodeAddr -> Maybe NodeAddr
incrementNodeAddr (NAAssumption n) = Just $ NAAssumption (n + 1)
incrementNodeAddr (NALine n) = Just $ NALine (n + 1)
incrementNodeAddr (NAProof n na) = NAProof n <$> incrementNodeAddr na
incrementNodeAddr _ = Nothing

paFromNA :: NodeAddr -> Proof -> Maybe ProofAddr
paFromNA (NALine n) _ = Just $ PAProof n
paFromNA NAConclusion (SubProof _ ps _) = Just $ PAProof (length ps)
paFromNA (NAProof n na) (SubProof _ ((!!? n) -> Just (Right p)) _) = PANested n <$> paFromNA na p
paFromNA _ _ = Nothing

paContaining :: NodeAddr -> Maybe ProofAddr
paContaining (NAProof n (NAAssumption{})) = Just $ PAProof n
paContaining (NAProof n (NALine{})) = Just $ PAProof n
paContaining (NAProof n NAConclusion) = Just $ PAProof n
paContaining (NAProof n NAAfterConclusion) = Just $ PAProof n
paContaining (NAProof n na) = PANested n <$> paContaining na
paContaining _ = Nothing

naFromPA :: ProofAddr -> (NodeAddr -> NodeAddr)
naFromPA (PAProof n) = NAProof n
naFromPA (PANested n pa) = NAProof n . naFromPA pa

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

-- * Querying proofs
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

holdsAt :: (a -> Bool) -> [a] -> Int -> Bool
holdsAt f xs n = maybe False f (xs !!? n)

-- | Returns `True` if the line at `NodeAddr` is the first formula of the proof.
pIsFirstFormula :: NodeAddr -> Proof -> Bool
pIsFirstFormula (NAAssumption 0) (SubProof fs _ _) = True
pIsFirstFormula (NAProof n na) (SubProof _ ps _) =
  holdsAt (either (const False) (pIsFirstFormula na)) ps n
pIsFirstFormula _ _ = False

-- | Returns `True` if the line at `NodeAddr` is a formula.
pIsFormula :: NodeAddr -> Proof -> Bool
pIsFormula (NAAssumption n) (SubProof fs _ _) = n < length fs
pIsFormula (NAProof n na) (SubProof _ ps _) =
  holdsAt (either (const False) (pIsFormula na)) ps n
pIsFormula _ _ = False

-- | Returns `True` if the line at `NodeAddr` is the last formula of the proof.
pIsLastFormula :: NodeAddr -> Proof -> Bool
pIsLastFormula (NAAssumption n) (SubProof fs _ _) = n == length fs - 1
pIsLastFormula (NAProof n na) (SubProof _ ps _) =
  holdsAt (either (const False) (pIsLastFormula na)) ps n
pIsLastFormula _ _ = False

-- | Returns `True` if the line at `NodeAddr` is the first `ProofLine` or `SubProof` in the proof.
pIsFirstLine :: NodeAddr -> Proof -> Bool
pIsFirstLine (NALine 0) (SubProof fs _ _) = True
pIsFirstLine (NAProof n na) (SubProof _ ps _) =
  holdsAt (either (const False) (pIsFirstLine na)) ps n
pIsFirstLine _ _ = False

-- | Returns `True` if the line at `NodeAddr` is a `ProofLine`
pIsLine :: NodeAddr -> Proof -> Bool
pIsLine (NALine n) (SubProof _ ps _) = holdsAt isLeft ps n
pIsLine (NAProof n na) (SubProof _ ps _) = holdsAt (either (const False) (pIsLine na)) ps n
pIsLine _ _ = False

-- | Returns `True` if the line at `NodeAddr` is a conclusion.
pIsConclusion :: NodeAddr -> Proof -> Bool
pIsConclusion NAConclusion _ = True
pIsConclusion (NAProof n na) (SubProof _ ps _) = holdsAt (either (const False) (pIsConclusion na)) ps n
pIsConclusion _ _ = False

{- | Returns the line at a given `NodeAddr`.

Returns `Nothing` if the `NodeAddr` does not specify a line of the proof.
-}
naLookup :: NodeAddr -> Proof -> Maybe (Either Assumption Derivation)
naLookup (NAAssumption n) (SubProof fs _ _) = Left <$> fs !!? n
naLookup (NALine n) (SubProof _ ((!!? n) -> Just (Left d)) _) = Just . Right $ d
naLookup NAConclusion (SubProof _ _ c) = Just . Right $ c
naLookup (NAProof n na) (SubProof _ ((!!? n) -> Just (Right p)) _) = naLookup na p
naLookup _ _ = Nothing

paLookup :: ProofAddr -> Proof -> Maybe Proof
paLookup (PANested n pa) (SubProof _ ((!!? n) -> Just (Right p)) _) = paLookup pa p
paLookup (PAProof n) (SubProof _ ((!!? n) -> Just (Right p)) _) = Just p
paLookup _ _ = Nothing

pIndex :: Int -> Proof -> Maybe (Either Assumption Derivation)
pIndex n p = case fromLineNo n p of
  Nothing -> Nothing
  Just addr -> case naLookup addr p of
    Nothing -> Nothing
    Just (Left a) -> Just (Left a)
    Just (Right d) -> Just . Right $ d

pIndexProof :: Int -> Int -> Proof -> Maybe Proof
pIndexProof start end p = fromLineRange start end p >>= (`paLookup` p)

pCollectAllNodeAddrs :: Proof -> [NodeAddr]
pCollectAllNodeAddrs = pSerializeLinesWithAddr const const

-- | naAffectsFreshness viewer viewee expresses whether viewee is relevant for checking freshness of viewer.
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

pCollectFreshnessNodes :: NodeAddr -> Proof -> Either Text [(NodeAddr, Either Assumption Derivation)]
pCollectFreshnessNodes na p = case mapM (\na -> (na,) <$> naLookup na p) $
  filter (naAffectsFreshness na) (pCollectAllNodeAddrs p) of
  Nothing -> Left "Internal error on pCollectFreshnessNodes, should not happen!"
  Just l -> Right l

-- * Updating proof contents

-- | `naUpdateFormula` @f@ @addr@ @proof@ replaces the formula at @addr@ in @proof@ using @f@.
naUpdateFormula :: Either (Assumption -> Assumption) (Formula -> Formula) -> NodeAddr -> Proof -> Maybe Proof
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

{- | `naUpdateRule` @f@ @addr@ @proof@ replaces the rule at @addr@ in @proof@ using @f@.

Fails silently
-}
naUpdateRule :: (Wrapper RuleApplication -> Wrapper RuleApplication) -> NodeAddr -> Proof -> Maybe Proof
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

{- | `naRemoveRaw` @addr@ @proof@ removes the element at @addr@ inside @proof@ if it exists.
Otherwise @proof@ is returned.

For conclusions, we take the following approach:

If the proof is otherwise empty (i.e. fs=[], ps=[]) the whole prove is removed.
Otherwise, the proof stays the same.
-}
naRemoveRaw :: NodeAddr -> Proof -> Maybe Proof
naRemoveRaw (NAAssumption n) (SubProof fs ps c) = liftA3 SubProof (removeAt n fs) (pure ps) (pure c)
naRemoveRaw (NALine n) (SubProof fs ps c) | holdsAt isLeft ps n = liftA3 SubProof (pure fs) (removeAt n ps) (pure c)
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

paRemoveRaw :: ProofAddr -> Proof -> Maybe Proof
paRemoveRaw (PAProof n) (SubProof fs ps c)
  | holdsAt isRight ps n =
      liftA3
        SubProof
        (pure fs)
        (removeAt n ps)
        (pure c)
paRemoveRaw (PANested n pa) (SubProof fs ps c) =
  liftA3
    SubProof
    (pure fs)
    (updateAtM n (either (const Nothing) (fmap Right . paRemoveRaw pa)) ps)
    (pure c)

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

paRemove :: ProofAddr -> Proof -> Maybe Proof
paRemove pa (lineRangeFromProofAddr pa -> Nothing) = Nothing
paRemove pa p@(lineRangeFromProofAddr pa -> Just (start, end)) = pMapRefs goRef <$> paRemoveRaw pa p
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

{- | `naInsertBeforeRaw` (`Left` @f@) @addr@ @proof@ inserts the given formula @f@ at the specified address @addr@ in @proof@.

`naInsertBeforeRaw` (`Right` @d@) @addr@ @proof@ inserts the given derivation @d@ at the specified address @addr@ in @proof@.

Both formulae and derivations are inserted before the specified address.
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
  fmap (NAAssumption n,) (liftA3 SubProof (insertAt (toAssumption d) n fs) (pure ps) (pure c))
-- Inserting before NALine
naInsertBeforeRaw (Left a) (NALine n) (SubProof fs ps c) =
  fmap (NALine n,) (liftA3 SubProof (pure fs) (insertAt (Left $ toDerivation a) n ps) (pure c))
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
        (liftA3 SubProof (pure fs) (updateAtM n (either (const Nothing) (const . pure $ Right p')) ps) (pure c))
naInsertBeforeRaw _ _ _ = Nothing

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
    Nothing -> ProofReference start end
    Just pa
      | lineNo > end -> ProofReference start end
      | naContainedIn na pa -> ProofReference start (end + 1)
      | lineNo <= start -> ProofReference (start + 1) (end + 1)

paInsertBeforeRaw ::
  Proof ->
  ProofAddr ->
  Proof ->
  Maybe (ProofAddr, Proof)
paInsertBeforeRaw p (PAProof n) (SubProof fs ps c) =
  fmap (PAProof n,) (liftA3 SubProof (pure fs) (insertAt (Right p) n ps) (pure c))
paInsertBeforeRaw p (PANested n pa) (SubProof fs ps@((!!? n) -> Just (Right prf)) c) =
  paInsertBeforeRaw p pa prf
    >>= \(pa, p') ->
      fmap
        (PANested n pa,)
        (liftA3 SubProof (pure fs) (updateAtM n (const . pure $ Right p') ps) (pure c))
paInsertBeforeRaw _ _ _ = Nothing

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
    Nothing -> ProofReference start end
    Just pa'
      | lineNo > end -> ProofReference start end
      | paContainedIn pa pa' -> ProofReference start (end + offset)
      | lineNo <= start -> ProofReference (start + offset) (end + offset)

{- | `naMoveBefore` @target@ @source@ @p@ moves the line at the source address
before the target line.
-}
naMoveBeforeRaw :: NodeAddr -> NodeAddr -> Proof -> Maybe (NodeAddr, Proof)
naMoveBeforeRaw targetAddr sourceAddr p =
  case (compare targetAddr sourceAddr, naLookup sourceAddr p) of
    (LT, Just node) -> do
      p' <- naRemoveRaw sourceAddr p
      naInsertBeforeRaw node targetAddr p'
    (GT, Just node) -> do
      -- since `e` is returned here already
      (na, p') <- naInsertBeforeRaw node targetAddr p
      p'' <- naRemoveRaw sourceAddr p'
      -- we might need to decrement `e` by one, if sourceAddr is in the same proof.
      let
        naDecrementWhenOnSameLevel :: NodeAddr -> NodeAddr -> NodeAddr
        naDecrementWhenOnSameLevel (NAAssumption n) NAAssumption{} = NAAssumption (n - 1)
        naDecrementWhenOnSameLevel (NALine n) NALine{} = NALine (n - 1)
        naDecrementWhenOnSameLevel (NAProof n na) NALine{} = NAProof (n - 1) na
        naDecrementWhenOnSameLevel (NAProof n na1) (NAProof m na2) | n == m = NAProof n $ naDecrementWhenOnSameLevel na1 na2
        naDecrementWhenOnSameLevel na _ = na
      pure (naDecrementWhenOnSameLevel na sourceAddr, p'')
    _ -> Nothing

targetInRange :: Int -> (Int, Int) -> Proof -> Bool
targetInRange lineNo (start, end) p =
  lineNo > start && lineNo <= end
    || lineNo == start
      && maybe False (maybe (const False) naInSameProof (fromLineNo start p)) (fromLineNo end p)

naMoveBefore :: NodeAddr -> NodeAddr -> Proof -> Maybe (NodeAddr, Proof)
naMoveBefore targetAddr sourceAddr p =
  if naCanMoveBefore p targetAddr (Left sourceAddr)
    then case naMoveBeforeRaw targetAddr sourceAddr p of
      Nothing -> Nothing
      Just (targetAddr', p') -> (targetAddr',) <$> go targetAddr' p'
    else Nothing
 where
  go :: NodeAddr -> Proof -> Maybe Proof
  go targetAddr' p' =
    case (fromNodeAddr targetAddr' p', fromNodeAddr sourceAddr p) of
      (Just target, Just source) -> pure $ pMapRefs (pure . goRef target source) p'
      _ ->
        -- Nothing
        error $
          "targetAddr'="
            <> show targetAddr'
            <> "\nsourceAddr="
            <> show sourceAddr
            <> "\np=\n"
            <> prettyPrint p
            <> "\np'=\n"
            <> prettyPrint p'
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

{- | `naCompatible` @target@ @source@ returns `True`
if @source@ and @target@ target are compatible, which means
that they are roughly of the same type.
i.e. assumptions can be moved before assumptions, proofs can be moved before lines etc.

Note that this does not exactly return if something can be moved somewhere, because
this function also returns true, when comparing a proof with its contents.
-}
naCompatible :: NodeAddr -> Either NodeAddr ProofAddr -> Bool
naCompatible (NAProof _ na) e = naCompatible na e
naCompatible _ (Left na) = True
naCompatible (NALine{}; NAConclusion) (Right pa) = True
naCompatible _ _ = False

naContainedIn :: NodeAddr -> ProofAddr -> Bool
naContainedIn (NAProof n _) (PAProof m) = n == m
naContainedIn (NAProof n na) (PANested m pa) = n == m && naContainedIn na pa
naContainedIn _ _ = False

paContainedIn :: ProofAddr -> ProofAddr -> Bool
paContainedIn (PANested n _) (PAProof m) = n == m
paContainedIn (PANested n pa1) (PANested m pa2) = n == m && paContainedIn pa1 pa2
paContainedIn _ _ = False

naSameOrNext :: NodeAddr -> Either NodeAddr ProofAddr -> Proof -> Bool
naSameOrNext (NAProof n na) (Left (NAProof ((== n) -> True) na')) (SubProof _ ((!!? n) -> Just (Right p)) _) =
  naSameOrNext na (Left na') p
naSameOrNext (NAProof n na) (Right (PANested ((== n) -> True) pa)) (SubProof _ ((!!? n) -> Just (Right p)) _) =
  naSameOrNext na (Right pa) p
naSameOrNext (NAAssumption n) (Left (NAAssumption m)) _ = n == m || n == m + 1
naSameOrNext (NALine n) (Left (NALine m)) _ = n == m || n == m + 1
naSameOrNext (NALine n) (Right (PAProof m)) _ = n == m || n == m + 1
naSameOrNext NAAfterConclusion (Left NAConclusion) _ = True
naSameOrNext NAConclusion (Left NAConclusion) _ = True
naSameOrNext NAConclusion (Left (NALine n)) (SubProof _ ps _) = n == length ps - 1
naSameOrNext NAConclusion (Right (PAProof n)) (SubProof _ ps _) = n == length ps - 1
naSameOrNext _ _ _ = False

naCanMoveConclusion :: Maybe NodeAddr -> NodeAddr -> Proof -> Bool
naCanMoveConclusion target NAConclusion (SubProof fs ps c) = case unsnoc ps of
  Nothing -> case fs of
    [] -> case target of
      Just NAAssumption{} -> False
      _ -> True
    _ -> False
  Just (_, Left _) -> True
  Just (_, Right _) -> False
naCanMoveConclusion na' (NAProof n na) (SubProof _ ((!!? n) -> Just (Right p)) _) = case na' of
  Just (NAProof m na'') | m == n -> naCanMoveConclusion (Just na'') na p
  _ -> naCanMoveConclusion Nothing na p
naCanMoveConclusion _ _ _ = True

naCanMoveBefore :: Proof -> NodeAddr -> Either NodeAddr ProofAddr -> Bool
naCanMoveBefore p na e =
  naCompatible na e
    && either (\n -> naCanMoveConclusion (Just na) n p) (const True) e
    && not (naSameOrNext na e p)
    && case e of
      Left _ -> True
      Right pa -> not $ naContainedIn na pa

paMoveBeforeRaw :: ProofAddr -> ProofAddr -> Proof -> Maybe (ProofAddr, Proof)
paMoveBeforeRaw targetAddr sourceAddr p = case (compare targetAddr sourceAddr, paLookup sourceAddr p) of
  (LT, Just prf) -> do
    p' <- paRemoveRaw sourceAddr p
    paInsertBeforeRaw prf targetAddr p'
  (GT, Just prf) -> do
    (pa, p') <- paInsertBeforeRaw prf targetAddr p
    p'' <- paRemoveRaw sourceAddr p'
    let
      paDecrementWhenOnSameLevel :: ProofAddr -> ProofAddr -> ProofAddr
      paDecrementWhenOnSameLevel (PAProof n) PAProof{} = PAProof (n - 1)
      paDecrementWhenOnSameLevel (PANested n pa) PAProof{} = PANested (n - 1) pa
      paDecrementWhenOnSameLevel (PANested n pa1) (PANested m pa2) | n == m = PANested n $ paDecrementWhenOnSameLevel pa1 pa2
      paDecrementWhenOnSameLevel na _ = na
    pure (paDecrementWhenOnSameLevel pa sourceAddr, p'')
  _ -> Nothing

inRange :: (Int, Int) -> Int -> Bool
inRange (start, end) n = n >= start && n <= end

paMoveBefore :: ProofAddr -> ProofAddr -> Proof -> Maybe (ProofAddr, Proof)
paMoveBefore targetAddr sourceAddr p = case paMoveBeforeRaw targetAddr sourceAddr p of
  Nothing -> Nothing
  Just (targetAddr', p') -> (targetAddr',) <$> go targetAddr' p'
 where
  go :: ProofAddr -> Proof -> Maybe Proof
  go targetAddr' p' = case (lineRangeFromProofAddr targetAddr' p', lineRangeFromProofAddr sourceAddr p) of
    (Just targetRange, Just sourceRange) -> pure $ pMapRefs (pure . goRef targetRange sourceRange) p'
    _ -> error $ "lineRangeFromProofAddr targetAddr' p'=" <> show (lineRangeFromProofAddr targetAddr' p') <> "\ntargetAddr'=" <> show targetAddr'
  goRef :: (Int, Int) -> (Int, Int) -> Reference -> Reference
  goRef (targetStart, targetEnd) (sourceStart, sourceEnd) (LineReference line)
    | inRange (sourceStart, sourceEnd) line = LineReference (targetStart + proofOffset)
    | line < sourceStart && targetStart <= line = LineReference (line + proofLen)
    | line > sourceEnd && targetEnd >= line = LineReference (line - proofLen)
    | otherwise = LineReference line
   where
    proofOffset = line - sourceStart
    proofLen = sourceEnd - sourceStart + 1
  goRef (targetStart, targetEnd) (sourceStart, sourceEnd) (ProofReference start end) = case fromLineRange start end p of
    Nothing -> ProofReference start end
    Just pa
      | start == sourceStart && end == sourceEnd -> ProofReference targetStart targetEnd
      | paContainedIn pa sourceAddr -> ProofReference (start + (targetStart - sourceStart)) (end + (targetEnd - sourceEnd))
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