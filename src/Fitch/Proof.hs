module Fitch.Proof where

import Data.Text qualified as T
import Relude.Extra.Map (toPairs)
import Relude.Extra.Newtype

-- * Definitions

class PrettyPrint a where
  prettyPrint :: a -> Text

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

type ProofSpec = ([FormulaSpec], FormulaSpec)

-- | The type of a fitch rule.
data RuleSpec
  = {- | A `RuleSpec` @assumptions@ @conclusion@ consists of
    a list of assumptions that are subproofs or formulae, and the conclusion.
    -}
    RuleSpec [FormulaSpec] [ProofSpec] FormulaSpec
  deriving (Show, Eq)

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
    go _ (FFreshVar n) = "[" <> n <> "]"
    go _ (FSubst f (Subst n t)) = f <> "[" <> n <> " -> " <> t <> "]"
    go True f = "(" <> go False f <> ")"
    go False (FInfixPredicate p t1 t2) = prettyPrint t1 <> " " <> p <> " " <> prettyPrint t2
    go False (FOpr op fs)
      | null fs = op
      | length fs == 2 = T.intercalate (" " <> op <> " ") (map (go True) fs)
      | otherwise = op <> "(" <> T.intercalate "," (map prettyPrint fs) <> ")"
    go False (FQuantifier q v f) = q <> " " <> v <> ". " <> prettyPrint f

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
  | -- | A fresh variable of a subproof, written like @[c]@
    FreshVar Name
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
    go False (FreshVar v) = "[" <> v <> "]"

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

newtype RawAssumption = RawAssumption RawFormula deriving (Eq, Show)

type Assumption = Wrapper RawAssumption

toAssumption :: Formula -> Assumption
toAssumption (Unparsed txt err) = Unparsed txt err
toAssumption (ParsedInvalid txt err f) = ParsedInvalid txt err (RawAssumption f)
toAssumption (ParsedValid txt f) = ParsedValid txt (RawAssumption f)

toFormula :: Assumption -> Formula
toFormula (Unparsed txt err) = Unparsed txt err
toFormula (ParsedInvalid txt err (RawAssumption f)) = ParsedInvalid txt err f
toFormula (ParsedValid txt (RawAssumption f)) = ParsedValid txt f

instance PrettyPrint RawAssumption where
  prettyPrint :: RawAssumption -> Text
  prettyPrint (RawAssumption f) = prettyPrint f

-- | Application of a rule
data RuleApplication
  = -- | Application of a rule, consisting of the `Name` of the rule, and a list of references.
    RuleApplication Name [Reference]
  deriving (Show, Eq)

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
  | NALine Int
  | NAProof Int NodeAddr
  deriving (Show, Eq)

isNAAssumption :: NodeAddr -> Bool
isNAAssumption (NAProof _ na) = isNAAssumption na
isNAAssumption (NAAssumption _) = True
isNAAssumption _ = False

isNAConclusion :: NodeAddr -> Bool
isNAConclusion (NAProof _ na) = isNAConclusion na
isNAConclusion NAConclusion = True
isNAConclusion _ = False

-- TODO comment
data ProofAddr
  = PAProof Int
  | PANested Int ProofAddr
  deriving (Show, Eq)

paProofToNested :: ProofAddr -> (ProofAddr -> ProofAddr)
paProofToNested (PAProof n) = PANested n
paProofToNested (PANested n pa) = PANested n

instance Ord NodeAddr where
  compare :: NodeAddr -> NodeAddr -> Ordering
  compare (NAAssumption n) (NAAssumption m) = compare n m
  compare (NAAssumption _) (NALine _) = LT
  compare (NALine _) (NAAssumption _) = GT
  compare (NALine n) (NALine m) = compare n m
  compare (NALine n) (NAProof m _) = compare n m
  compare (NAProof n _) (NALine m) = compare n m
  compare (NAAssumption _) (NAProof _ _) = LT
  compare (NAProof _ _) (NAAssumption _) = GT
  compare (NAProof n addr1) (NAProof m addr2) | n == m = compare addr1 addr2
  compare (NAProof n _) (NAProof m _) = compare n m
  compare NAConclusion NAConclusion = EQ
  compare NAConclusion a = GT
  compare a NAConclusion = LT

compareNaPa :: NodeAddr -> ProofAddr -> Ordering
compareNaPa (NAAssumption n) _ = LT
compareNaPa (NALine n) (PAProof m) = compare n m
compareNaPa (NALine n) (PANested m pa) = compare n m
compareNaPa NAConclusion _ = GT
compareNaPa (NAProof n na) (PAProof m) = compare n m
compareNaPa (NAProof n na) (PANested m pa) | n == m = compareNaPa na pa
compareNaPa (NAProof n _) (PANested m _) = compare n m

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
  helper n m (Right p : ps) | (n - 1) < pLength p = do
    addr <- fromLineNo n p
    pure $ NAProof m addr
  helper n m (Right p : ps) = helper (n - pLength p) (m + 1) ps
fromLineNo n (SubProof fs _ _) | (n - 1) < length fs = Just $ NAAssumption (n - 1)
fromLineNo n (SubProof fs ps l) = fromLineNo (n - length fs) (SubProof [] ps l)

fromLineRange :: Int -> Int -> Proof -> Maybe ProofAddr
fromLineRange start end p = go start end 0 p
 where
  go :: Int -> Int -> Int -> Proof -> Maybe ProofAddr
  go start end _ _ | start < 1 || end <= start = Nothing
  go 1 end n p = do
    first <- fromLineNo 1 p
    last <- fromLineNo end p
    pa1 <- paFromNA first
    pa2 <- paFromNA last
    if pIsFirstFormula first p
      && pIsConclusion last p
      && pa1 == pa2
      then Just pa1
      else Nothing
  go start end n (SubProof [] (Left d : ps) c) = go (start - 1) (end - 1) (n + 1) (SubProof [] ps c)
  go start end n (SubProof [] (Right p : ps) c)
    | pLength p < start = go (start - pLength p) (end - pLength p) (n + 1) (SubProof [] ps c)
    | otherwise = PANested n <$> go start end 0 p
  go start end n (SubProof fs ps c) = go (start - length fs) (end - length fs) n (SubProof [] ps c)

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
  go n (NAProof m na) (SubProof fs ps _) = case ps !!? m of
    Just (Right p) -> go (length fs + n + foldr (\p n -> either (const $ n + 1) ((n +) . pLength) p) 0 (take m ps)) na p
    _ -> Nothing
  go _ _ _ = Nothing

lineNoOr999 :: NodeAddr -> Proof -> Int
lineNoOr999 na p = fromMaybe 999 (fromNodeAddr na p)

-- ** Utilities for working with addresses

-- | `incrementNodeAddr` increments an address by 1, while keeping the nesting structure unchanged.
incrementNodeAddr :: NodeAddr -> Maybe NodeAddr
incrementNodeAddr (NAAssumption n) = Just $ NAAssumption (n + 1)
incrementNodeAddr (NALine n) = Just $ NALine (n + 1)
incrementNodeAddr (NAProof n na) = NAProof n <$> incrementNodeAddr na
incrementNodeAddr NAConclusion = Nothing

paFromNA :: NodeAddr -> Maybe ProofAddr
paFromNA (NAProof n (NAAssumption{})) = Just $ PAProof n
paFromNA (NAProof n (NALine{})) = Just $ PAProof n
paFromNA (NAProof n NAConclusion) = Just $ PAProof n
paFromNA (NAProof n na) = PANested n <$> paFromNA na
paFromNA _ = Nothing

naFromPA :: ProofAddr -> (NodeAddr -> NodeAddr)
naFromPA (PAProof n) = NAProof n
naFromPA (PANested n pa) = NAProof n . naFromPA pa

naLevelup2 :: NodeAddr -> Maybe (NodeAddr -> NodeAddr)
naLevelup2 = go id
 where
  go :: (NodeAddr -> NodeAddr) -> NodeAddr -> Maybe (NodeAddr -> NodeAddr)
  go na (NAProof _ NAConclusion) = Just na
  go na (NAProof _ (NAAssumption _)) = Just na
  go na (NAProof _ (NALine _)) = Just na
  go na (NAProof m na') = go (na . NAProof m) na'
  go _ _ = Nothing

-- * Querying proofs

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
pIndexProof start end p = do
  startA <- fromLineNo start p
  endA <- fromLineNo end p
  pa1 <- paFromNA startA
  pa2 <- paFromNA endA
  if pIsFirstFormula startA p
    && pIsConclusion endA p
    && pa1 == pa2
    then paLookup pa1 p
    else Nothing

pCollectAllNodeAddrs :: Proof -> [NodeAddr]
pCollectAllNodeAddrs = pSerializeLinesWithAddr const const

-- | naAffectsFreshness viewer viewee expresses whether viewee is relevant for checking freshness of viewer.
naAffectsFreshness :: NodeAddr -> NodeAddr -> Bool
naAffectsFreshness (NAProof n na1) (NAProof m na2)
  | n > m = True
  | n == m = naAffectsFreshness na1 na2
  | n < m = False
naAffectsFreshness (NAProof _ (NAAssumption{}; NALine{}; NAConclusion)) (NAAssumption{}; NALine{}; NAConclusion) = True
naAffectsFreshness (NAProof{}) (NAAssumption{}) = False
naAffectsFreshness (NAProof n _) (NALine m) = m < n
naAffectsFreshness (NAProof{}) _ = False
naAffectsFreshness (NAAssumption n) (NAAssumption m) = m < n
naAffectsFreshness (NAAssumption _) (NALine{}; NAConclusion) = False
naAffectsFreshness _ _ = False

pCollectFreshnessNodes :: NodeAddr -> Proof -> Either Text [(NodeAddr, Either Assumption Derivation)]
pCollectFreshnessNodes na p = case mapM (\na -> (na,) <$> naLookup na p) $ filter (naAffectsFreshness na) (pCollectAllNodeAddrs p) of
  Nothing -> Left "Internal error on pCollectFreshnessNodes, should not happen!"
  Just l -> Right l

extractFormula :: Either Assumption Derivation -> Maybe RawFormula
extractFormula (Left a) = un $ fromWrapper a
extractFormula (Right (Derivation f _)) = fromWrapper f

extractText :: Either Assumption Derivation -> Text
extractText (Left a) = getText a
extractText (Right (Derivation f _)) = getText f

-- * Updating proof contents

{- | `naUpdateFormula` @f@ @addr@ @proof@ replaces the formula at @addr@ in @proof@ using @f@.

Fails silently
-}
naUpdateFormula :: Either (Assumption -> Assumption) (Formula -> Formula) -> NodeAddr -> Proof -> Proof
naUpdateFormula (Left f) (NAAssumption n) (SubProof fs ps l) = SubProof (updateAt n f fs) ps l
naUpdateFormula (Right f) (NALine n) (SubProof fs ps l) =
  SubProof
    fs
    ( updateAt
        n
        ( either
            ( Left . \(Derivation formula rule) ->
                Derivation (f formula) rule
            )
            Right
        )
        ps
    )
    l
naUpdateFormula (Right f) NAConclusion (SubProof fs ps (Derivation formula rule)) =
  SubProof fs ps (Derivation (f formula) rule)
naUpdateFormula f (NAProof n na) (SubProof fs ps l) =
  SubProof fs (updateAt n (fmap (naUpdateFormula f na)) ps) l
naUpdateFormula _ _ p = p

{- | `naUpdateRule` @f@ @addr@ @proof@ replaces the rule at @addr@ in @proof@ using @f@.

Fails silently
-}
naUpdateRule :: (Wrapper RuleApplication -> Wrapper RuleApplication) -> NodeAddr -> Proof -> Proof
naUpdateRule f (NALine n) (SubProof fs ps l) =
  SubProof
    fs
    ( updateAt
        n
        ( either
            ( Left . \(Derivation formula rule) ->
                Derivation formula (f rule)
            )
            Right
        )
        ps
    )
    l
naUpdateRule f NAConclusion (SubProof fs ps (Derivation formula rule)) =
  SubProof fs ps (Derivation formula (f rule))
naUpdateRule f (NAProof n na) (SubProof fs ps l) =
  SubProof fs (updateAt n (fmap (naUpdateRule f na)) ps) l

-- -- * (Re-)moving inside a proof

{- | `naRemove` @addr@ @proof@ removes the element at @addr@ inside @proof@ if it exists (and is not a conclusion).
Otherwise @proof@ is returned.
-}
naRemove :: NodeAddr -> Proof -> Proof
naRemove (NAAssumption n) (SubProof fs ps c) = SubProof (removeAt n fs) ps c
naRemove (NALine n) (SubProof fs ps c) | holdsAt isLeft ps n = SubProof fs (removeAt n ps) c
naRemove (NAProof n na) (SubProof fs ps c) = SubProof fs (updateAt n (fmap (naRemove na)) ps) c
naRemove _ p = p

paRemove :: ProofAddr -> Proof -> Proof
paRemove (PAProof n) (SubProof fs ps c) | holdsAt isRight ps n = SubProof fs (removeAt n ps) c
paRemove (PANested n pa) (SubProof fs ps c) = SubProof fs (updateAt n (fmap (paRemove pa)) ps) c

{- | `naInsertBefore` (`Left` @f@) @addr@ @proof@ inserts the given formula @f@ at the specified address @addr@ in @proof@.

`naInsertBefore` (`Right` @d@) @addr@ @proof@ inserts the given derivation @d@ at the specified address @addr@ in @proof@.

Both formulae and derivations are inserted before the specified address.
-}
naInsertBefore ::
  Either Assumption (Either Derivation Proof) ->
  NodeAddr ->
  Proof ->
  Maybe (Either NodeAddr ProofAddr, Proof)
naInsertBefore (Left a) (NAAssumption n) (SubProof fs ps c) =
  Just (Left $ NAAssumption n, SubProof (insertAt a n fs) ps c)
naInsertBefore (Right (Left (Derivation f _))) (NAAssumption n) (SubProof fs ps c) =
  Just (Left $ NAAssumption n, SubProof (insertAt (toAssumption f) n fs) ps c)
naInsertBefore (Left a) (NALine n) (SubProof fs ps c) =
  Just (Left $ NALine n, SubProof fs (insertAt d n ps) c)
 where
  d = Left $ Derivation (toFormula a) (Unparsed "(?)" "")
naInsertBefore (Right (Left d)) (NALine n) (SubProof fs ps c) =
  Just (Left $ NALine n, SubProof fs (insertAt (Left d) n ps) c)
naInsertBefore (Right (Right p)) (NALine n) (SubProof fs ps c) =
  Just (Right $ PAProof n, SubProof fs (insertAt (Right p) n ps) c)
naInsertBefore e (NAProof n na) (SubProof fs ps c) = case ps !!? n of
  Just (Right p) ->
    naInsertBefore e na p
      >>= ( \(addr, p') -> case addr of
              Left na ->
                pure (Left $ NAProof n na, SubProof fs (updateAt n (const $ Right p') ps) c)
              Right pa ->
                pure (Right $ PANested n pa, SubProof fs (updateAt n (const $ Right p') ps) c)
          )
  _ -> Nothing
naInsertBefore _ _ _ = Nothing

-- naInsertBefore :: Either Assumption (Either Derivation Proof) -> NodeAddr -> Proof -> Maybe Proof
-- naInsertBefore (Left f) (NAAssumption n) (SubProof fs ps c) = Just $ SubProof (insertAt f n fs) ps c
-- naInsertBefore (Right p) (NALine n) (SubProof fs ps c) = Just $ SubProof fs (insertAt p n ps) c
-- naInsertBefore e (NAProof n a) (SubProof fs ps c) = case ps !!? n of
--   Just (Right p) ->
--     naInsertBefore e a p
--       >>= ( \p' ->
--               pure $ SubProof fs (updateAt n (const $ Right p') ps) c
--           )
--   _ -> Nothing
-- naInsertBefore _ _ _ = Nothing

{- | `naMove` @target@ @source@ @p@ moves the line at the source address
either before the target line.
-}
naMove :: NodeAddr -> NodeAddr -> Proof -> Proof
naMove targetAddr sourceAddr p = case (compare targetAddr sourceAddr, naLookup sourceAddr p) of
  (LT, Just node)
    | not (pIsConclusion sourceAddr p) ->
        let p' = naRemove sourceAddr p
         in case naInsertBefore (fmap Left node) targetAddr p' of
              Just (_, p') -> p'
              _ -> p
  (GT, Just node)
    | not (pIsConclusion sourceAddr p) ->
        maybe p (naRemove sourceAddr) $ case naInsertBefore (fmap Left node) targetAddr p of
          Just (_, p') -> Just p'
          _ -> Nothing
  _ -> p

paMove :: NodeAddr -> ProofAddr -> Proof -> Proof
paMove targetAddr sourceAddr p = case (compareNaPa targetAddr sourceAddr, paLookup sourceAddr p) of
  (LT, Just prf) ->
    let p' = paRemove sourceAddr p
     in case naInsertBefore (Right $ Right prf) targetAddr p' of
          Just (_, p') -> p'
          _ -> p
  (GT, Just prf) -> maybe p (paRemove sourceAddr) $ case naInsertBefore (Right $ Right prf) targetAddr p of
    Just (_, p') -> Just p'
    _ -> Nothing
  _ -> p

-- * Utilities that are not exported!

{- | `insertAt` @x@ @n@ @xs@ inserts @x@ at index @n@ into @xs@.

Fails for @n < 0@, returns @xs@ for @n > length xs@.
-}
insertAt :: a -> Int -> [a] -> [a]
insertAt x 0 xs = x : xs
insertAt x n [] = [x]
insertAt x n (y : ys) = y : insertAt x (n - 1) ys

{- | `removeAt` @n@ @xs@ removes the element at index @n@.

Returns @xs@ for invalid indices.
-}
removeAt :: Int -> [a] -> [a]
removeAt n [] = []
removeAt n (x : xs)
  | n < 0 = x : xs
  | n == 0 = xs
  | n > 0 = x : removeAt (n - 1) xs

{- | Update nth element of a list, if it exists.
  @O(min index n)@.

  Precondition: the index is >= 0.
  (Copied from Agda.Utils.List)
-}
updateAt :: Int -> (a -> a) -> [a] -> [a]
updateAt _ _ [] = []
updateAt 0 f (a : as) = f a : as
updateAt n f (a : as) = a : updateAt (n - 1) f as