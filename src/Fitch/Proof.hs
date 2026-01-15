module Fitch.Proof where

import Control.Monad (foldM, join, liftM3, liftM4, when)
import Data.List qualified as L
import Data.Maybe (fromJust, fromMaybe, isJust)
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import Data.Traversable (mapAccumL)

-- * Definitions

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
fromWrapper :: Wrapper a -> a
fromWrapper (ParsedValid _ x) = x
fromWrapper (ParsedInvalid _ _ x) = x
fromWrapper (Unparsed{}) = error "fromWrapper called on Unparsed"

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
  deriving (Eq, Ord)

instance Show Term where
  show :: Term -> String
  show (Var v) = T.unpack v
  show (Fun f []) = T.unpack f
  show (Fun f ts) = T.unpack f ++ "(" ++ L.intercalate "," (map show ts) ++ ")"

data Subst a = Subst Name a
  deriving (Show, Eq)

infixl 9 ~>
(~>) :: Name -> a -> Subst a
(~>) = Subst

data TermSpec
  = TVar Name
  | TFun Name [TermSpec]
  | TPlaceholder Name
  deriving (Eq)

instance Show TermSpec where
  show :: TermSpec -> String
  show (TVar n) = T.unpack n
  show (TFun f ts) = T.unpack f ++ "(" ++ L.intercalate "," (map show ts) ++ ")"
  show (TPlaceholder n) = T.unpack n

data FormulaSpec
  = FSubst Name (Subst TermSpec)
  | FPlaceholder Name
  | FPredicate Name [TermSpec]
  | FOp Text [FormulaSpec]
  | FQuantifier Name Name FormulaSpec
  | FFreshVar Name
  deriving (Eq)

instance Show FormulaSpec where
  show :: FormulaSpec -> String
  show f = go False f
   where
    go :: Bool -> FormulaSpec -> String
    go _ (FPredicate p []) = T.unpack p
    go _ (FPredicate p ts) = T.unpack p ++ "(" ++ L.intercalate "," (map show ts) ++ ")"
    go _ (FPlaceholder n) = T.unpack n
    go _ (FFreshVar n) = "[" ++ T.unpack n ++ "]"
    go _ (FSubst f (Subst n t)) = T.unpack f ++ "[" ++ T.unpack n ++ " -> " ++ show t ++ "]"
    go True f = "(" ++ go False f ++ ")"
    go _ (FOp op fs)
      | null fs = T.unpack op
      | L.length fs == 2 = L.intercalate (" " ++ T.unpack op ++ " ") (map (go True) fs)
      | otherwise = T.unpack op ++ "(" ++ L.intercalate "," (map show fs) ++ ")"
    go _ (FQuantifier q v f) = T.unpack q ++ " " ++ T.unpack v ++ ". " ++ show f

-- | A formula for first-order logic (can be instantiated to 0th order, by using `Predicate` without the list of `Term`.
data Formula
  = -- | A single `Predicate` applied to terms
    Predicate Name [Term]
  | -- | A n-ary operator, like @->@ for implication, or @~@ for negation.
    Op Text [Formula]
  | -- | A quantifier, like @∀@ for universal quantification.
    Quantifier Name Name Formula
  | -- | A fresh variable of a subproof, written like @[c]@
    FreshVar Name
  deriving (Eq, Ord)

instance Show Formula where
  show :: Formula -> String
  show f = go False f
   where
    go :: Bool -> Formula -> String
    go _ (Predicate p []) = T.unpack p
    go _ (Predicate p ts) = T.unpack p ++ "(" ++ L.intercalate "," (map show ts) ++ ")"
    go True f = "(" ++ go False f ++ ")"
    go _ (Op op fs)
      | null fs = T.unpack op
      | L.length fs == 2 = L.intercalate (T.unpack op) (map (go True) fs)
      | otherwise = T.unpack op ++ "(" ++ L.intercalate "," (map show fs) ++ ")"
    go _ (Quantifier q v f) = T.unpack q ++ " " ++ T.unpack v ++ ". " ++ show f
    go _ (FreshVar v) = "[" ++ T.unpack v ++ "]"

-- | A reference to a line (either `Assumption` or `ProofLine`) or a `SubProof`
data Reference where
  -- | Referencing a single line
  LineReference :: Int -> Reference
  -- | Referencing a subproof by a line interval, i.e. `ProofReference` @from@ @to@
  ProofReference :: Int -> Int -> Reference
  deriving (Show, Eq)

-- | Assumptions are formulae wrapped with parsing and semantic information.
type Assumption = Wrapper Formula

-- | Application of a rule
data RuleApplication
  = -- | Application of a rule, consisting of the `Name` of the rule, and a list of references.
    RuleApplication Name [Reference]
  deriving (Show, Eq)

-- | A derivation inside a proof.
data Derivation
  = {- | A derivation inside a proof, i.e. a single line consisting of a formula
    and a ruleapplication that justifies how the formula was derived.
    -}
    Derivation Assumption (Wrapper RuleApplication)
  deriving (Show, Eq)

-- | A datatype for respresenting fitch-style proofs.
data Proof where
  -- | A single line of the proof consisting of a derivation.
  ProofLine :: Derivation -> Proof
  -- | A subproof consisting of a list of assumptions, a list of subproofs (or derivations) and a conclusion.
  SubProof :: [Assumption] -> [Proof] -> Derivation -> Proof
  deriving (Eq)

instance Show Proof where
  show :: Proof -> String
  show = show' 1 0
   where
    withIndent :: Int -> Int -> String -> String
    withIndent line level s = (if line < 0 then "  " else show line ++ replicate ((2 :: Int) - length (show line)) ' ') ++ concat (replicate level "  |") ++ "  |" ++ s ++ "\n"
    showProof :: Int -> Int -> Proof -> String
    showProof line level p@(ProofLine _) = withIndent line level $ show' line level p
    showProof line level p@(SubProof{}) = show' line (level + 1) p
    show' :: Int -> Int -> Proof -> String
    show' line level (ProofLine (Derivation f r)) = show f ++ show r
    show' line level (SubProof fs ps l) = concat fsShow ++ withIndent (-1) level "------" ++ concat psShow ++ conclusionShow
     where
      (line', fsShow) = L.mapAccumL (\ln f -> (ln + 1, withIndent ln level $ show f)) line fs
      (line'', psShow) = L.mapAccumL (\ln' p -> (ln' + pLength p, showProof ln' level p)) line' ps
      conclusionShow = withIndent line'' level (show' line'' level (ProofLine l))

-- | Returns `True` if the proof is a `SubProof`
isSubProof :: Proof -> Bool
isSubProof (SubProof{}) = True
isSubProof _ = False

-- | Returns `True` if the proof is a `ProofLine`
isProofLine :: Proof -> Bool
isProofLine (ProofLine{}) = True
isProofLine _ = False

-- | The `pLength` of a proof is its number of lines.
pLength :: Proof -> Int
pLength = pFold (\n _ -> n + 1) (\n _ -> n + 1) 0

-- * Folding and mapping proofs

-- | `pFold` @af@ @df@ @s@ @p@ folds the proof @p@, i.e. it reduces it line-wise to a value of type `a` with starting value @s@.
pFold ::
  (a -> Assumption -> a) ->
  (a -> Derivation -> a) ->
  a ->
  Proof ->
  a
pFold af df s (ProofLine d) = df s d
pFold af df s (SubProof fs ps d) = df (foldl' (pFold af df) (foldl' af s fs) ps) d

-- | `pSerialize` @af@ @df@ @p@ serializes the proof @p@ by applying a function for each line in the proof and storing the results in a list.
pSerialize :: (Assumption -> a) -> (Derivation -> a) -> Proof -> [a]
pSerialize af df (ProofLine d) = [df d]
pSerialize af df (SubProof fs ps d) = map af fs ++ concatMap (pSerialize af df) ps ++ [df d]

-- | Like `pSerialize` but the current `NodeAddr` is dragged along.
pSerializeWithAddr :: (Assumption -> NodeAddr -> a) -> (Derivation -> NodeAddr -> a) -> Proof -> [a]
pSerializeWithAddr = go Nothing
 where
  go :: Maybe NodeAddr -> (Assumption -> NodeAddr -> a) -> (Derivation -> NodeAddr -> a) -> Proof -> [a]
  go Nothing af df (ProofLine d) = [df d (NAProof 0 Nothing)]
  go (Just addr) af df (ProofLine d) = [df d addr]
  go mna af df (SubProof fs ps d) = mappedFs ++ concat mappedPs ++ [df d (naAppendConclusion mna)]
   where
    (_, mappedFs) = mapAccumL (\m frm -> (m + 1, af frm (naAppendAssumption m mna))) 0 fs
    (_, mappedPs) = mapAccumL (\m prf -> (m + 1, go (Just $ naAppendProof m mna) af df prf)) 0 ps

-- | `pMap` @af@ @df@ @p@ maps each line of the proof @p@ using functions @af@ and @df@.
pMap ::
  (Assumption -> Assumption) ->
  (Derivation -> Derivation) ->
  Proof ->
  Proof
pMap af df (ProofLine d) = ProofLine $ df d
pMap af df (SubProof fs ps d) = SubProof (map af fs) (map (pMap af df) ps) (df d)

pMapAccumL ::
  (s -> Assumption -> (s, Assumption)) ->
  (s -> Derivation -> (s, Derivation)) ->
  s ->
  Proof ->
  (s, Proof)
pMapAccumL af df s (ProofLine d) =
  let
    (s', d') = df s d
   in
    (s', ProofLine d')
pMapAccumL af df s (SubProof fs ps d) =
  let
    (s', fs') = mapAccumL af s fs
    (s'', ps') = mapAccumL (pMapAccumL af df) s' ps
    (s''', d') = df s'' d
   in
    (s''', SubProof fs' ps' d')

pMapWithLineNo ::
  (Int -> Assumption -> Assumption) ->
  (Int -> Derivation -> Derivation) ->
  Proof ->
  Proof
pMapWithLineNo af df = snd . pMapAccumL af' df' 1
 where
  af' :: Int -> Assumption -> (Int, Assumption)
  af' n a = (n + 1, af n a)
  df' :: Int -> Derivation -> (Int, Derivation)
  df' n d = (n + 1, df n d)

-- | Like `pMap` but lifted to monadic results.
pMapM ::
  (Monad m) =>
  (Assumption -> m Assumption) ->
  (Derivation -> m Derivation) ->
  Proof ->
  m Proof
pMapM af df (ProofLine d) = ProofLine <$> df d
pMapM af df (SubProof fs ps d) =
  liftM3
    SubProof
    (mapM af fs)
    (mapM (pMapM af df) ps)
    (df d)

-- | Like `pMapM` but an accumulator is dragged along.
pMapMAccumL ::
  (Monad m) =>
  (s -> Assumption -> m (s, Assumption)) ->
  (s -> Derivation -> m (s, Derivation)) ->
  s ->
  Proof ->
  m (s, Proof)
pMapMAccumL af df s (ProofLine d) = do
  (s', d') <- df s d
  return (s', ProofLine d')
pMapMAccumL af df s (SubProof fs ps d) = do
  (s', fs') <-
    foldM
      (\(t, fs') f -> af t f >>= (\(t', f') -> return (t', fs' ++ [f'])))
      (s, [])
      fs
  (s'', ps') <-
    foldM
      ( \(t, ps') p ->
          pMapMAccumL af df t p >>= (\(t', p') -> return (t', ps' ++ [p']))
      )
      (s', [])
      ps
  (s''', d') <- df s'' d
  return (s''', SubProof fs' ps' d')

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
  | NAProof Int (Maybe NodeAddr)
  deriving (Show, Eq)

instance Ord NodeAddr where
  compare :: NodeAddr -> NodeAddr -> Ordering
  compare (NAAssumption n) (NAAssumption m) = compare n m
  compare (NAAssumption _) (NAProof _ Nothing) = LT
  compare (NAProof _ Nothing) (NAAssumption _) = GT
  compare (NAProof n Nothing) (NAProof m Nothing) = compare n m
  compare (NAProof n Nothing) (NAProof m _) = compare n m
  compare (NAProof n _) (NAProof m Nothing) = compare n m
  compare (NAAssumption _) (NAProof _ _) = LT
  compare (NAProof _ _) (NAAssumption _) = GT
  compare (NAProof n (Just addr1)) (NAProof m (Just addr2)) | n == m = compare addr1 addr2
  compare (NAProof n _) (NAProof m _) = compare n m
  compare NAConclusion NAConclusion = EQ
  compare NAConclusion a = GT
  compare a NAConclusion = LT

-- ** Conversion between line numbers and `NodeAddr`

{- | Takes a line index and returns the corresponding `NodeAddr` for a given proof.

NOTE: indices of NodeAddr start at 0, but line numbers start at 1!
-}
fromLineNo :: Int -> Proof -> Maybe NodeAddr
fromLineNo n _ | n < 1 = Nothing
fromLineNo 1 (ProofLine{}) = Just $ NAProof 0 Nothing
fromLineNo n (SubProof [] ps _) = helper n 0 ps
 where
  helper :: Int -> Int -> [Proof] -> Maybe NodeAddr
  helper 1 _ [] = Just NAConclusion
  helper n _ [] = Nothing
  helper 1 m ((ProofLine{}) : ps) = Just $ NAProof m Nothing
  helper n m (p : ps) | (n - 1) < pLength p = do
    addr <- fromLineNo n p
    return $ NAProof m (Just addr)
  helper n m (p : ps) = helper (n - pLength p) (m + 1) ps
fromLineNo n (SubProof fs _ _) | (n - 1) < L.length fs = Just $ NAAssumption (n - 1)
fromLineNo n (SubProof fs ps l) = fromLineNo (n - L.length fs) (SubProof [] ps l)
fromLineNo n p = Nothing

fromLineRange :: Int -> Int -> Proof -> Maybe NodeAddr
fromLineRange start end p = go start end 0 p
 where
  go :: Int -> Int -> Int -> Proof -> Maybe NodeAddr
  go _ _ _ (ProofLine{}) = Nothing
  go start end _ _ | start < 1 || end <= start = Nothing
  go 1 end n p = do
    first <- fromLineNo 1 p
    last <- fromLineNo end p
    na1 <- naLevelUp first
    na2 <- naLevelUp last
    if pIsFirstFormula first p
      && pIsConclusion last p
      && na1 == na2
      then Just na1
      else Nothing
  go start end n (SubProof [] (p : ps) c)
    | pLength p < start = go (start - pLength p) (end - pLength p) (n + 1) (SubProof [] ps c)
    | otherwise = NAProof n . Just <$> go start end 0 p
  go start end n (SubProof fs ps c) = go (start - length fs) (end - length fs) n (SubProof [] ps c)

{- | Takes a `NodeAddr` and returns the corresponding line index for a given proof.

NOTE: indices of NodeAddr start at 0, but line numbers start at 1!
-}
fromNodeAddr :: NodeAddr -> Proof -> Maybe Int
fromNodeAddr = go 1
 where
  go :: Int -> NodeAddr -> Proof -> Maybe Int
  go 1 (NAProof 0 Nothing) (ProofLine{}) = Just 1
  go n (NAAssumption m) (SubProof fs _ _) | m < L.length fs = return $ n + m
  go n (NAAssumption m) (SubProof fs _ _) = Nothing
  go 1 (NAProof 0 Nothing) (SubProof [] [] _) = Just 1
  go n (NAProof m Nothing) (SubProof fs ps _) | m < L.length ps && isProofLine (ps !! m) = return $ L.length fs + n + foldr (\p n -> n + pLength p) 0 (take m ps)
  go n NAConclusion (SubProof fs ps _) = return $ L.length fs + n + foldr (\p n -> n + pLength p) 0 ps
  go n (NAProof m (Just addr)) (SubProof fs ps _) | m < L.length ps && isSubProof (ps !! m) = go (L.length fs + n + foldr (\p n -> n + pLength p) 0 (take m ps)) addr (ps !! m)
  go _ _ _ = Nothing

-- ** Utilities for working with addresses

{- | Appends an assumption inside the `NodeAddr`, if no `NodeAddr` is given, returns `NAAssumption` @m@

Fails if the `NodeAddr` does not allow appending (e.g. `NAConclusion`)
-}
naAppendAssumption :: Int -> Maybe NodeAddr -> NodeAddr
naAppendAssumption m Nothing = NAAssumption m
naAppendAssumption m (Just (NAProof n a)) = NAProof n (Just $ naAppendAssumption m a)
naAppendAssumption m a = error $ show a ++ "\n cannot append assumption."

{- | Appends an empty proof inside the `NodeAddr`, if no `NodeAddr` is given, returns `NAProof` @m@ `Nothing`

Fails if the `NodeAddr` does not allow appending (e.g. `NAConclusion`)
-}
naAppendProof :: Int -> Maybe NodeAddr -> NodeAddr
naAppendProof m Nothing = NAProof m Nothing
naAppendProof m (Just (NAProof n a)) = NAProof n (Just $ naAppendProof m a)
naAppendProof m a = error $ show a ++ "\n cannot append line."

{- | Appends a conclusion inside the `NodeAddr`, if no `NodeAddr` is given, returns `NAConclusion`

Fails if the `NodeAddr` does not allow appending (e.g. `NAConclusion`)
-}
naAppendConclusion :: Maybe NodeAddr -> NodeAddr
naAppendConclusion Nothing = NAConclusion
naAppendConclusion (Just (NAProof n a)) = NAProof n (Just $ naAppendConclusion a)
naAppendConclusion a = error $ show a ++ "\n cannot append conclusion."

-- | `incrementNodeAddr` increments an address by 1, while keeping the nesting structure unchanged.
incrementNodeAddr :: NodeAddr -> NodeAddr
incrementNodeAddr (NAAssumption n) = NAAssumption (n + 1)
incrementNodeAddr (NAProof n Nothing) = NAProof (n + 1) Nothing
incrementNodeAddr (NAProof n (Just a)) = NAProof n (Just (incrementNodeAddr a))

naLevelUp :: NodeAddr -> Maybe NodeAddr
naLevelUp (NAProof n (Just (NAAssumption{}))) = Just $ NAProof n Nothing
naLevelUp (NAProof n (Just NAConclusion)) = Just $ NAProof n Nothing
naLevelUp (NAProof n (Just (NAProof _ Nothing))) = Just $ NAProof n Nothing
naLevelUp (NAProof n (Just na)) = Just . NAProof n $ naLevelUp na
naLevelUp _ = Nothing

-- * Querying proofs

-- | Returns `True` if the line at `NodeAddr` is the first formula of the proof.
pIsFirstFormula :: NodeAddr -> Proof -> Bool
pIsFirstFormula (NAAssumption 0) (SubProof fs _ _) = True
pIsFirstFormula (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && pIsFirstFormula a (ps !! n)
pIsFirstFormula _ _ = False

-- | Returns `True` if the line at `NodeAddr` is a formula.
pIsFormula :: NodeAddr -> Proof -> Bool
pIsFormula (NAAssumption n) (SubProof fs _ _) = n < L.length fs
pIsFormula (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && pIsFormula a (ps !! n)
pIsFormula _ _ = False

-- | Returns `True` if the line at `NodeAddr` is the last formula of the proof.
pIsLastFormula :: NodeAddr -> Proof -> Bool
pIsLastFormula (NAAssumption n) (SubProof fs _ _) = n == L.length fs - 1
pIsLastFormula (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && pIsLastFormula a (ps !! n)
pIsLastFormula _ _ = False

-- | Returns `True` if the line at `NodeAddr` is the first `ProofLine` or `SubProof` in the proof.
pIsFirstLine :: NodeAddr -> Proof -> Bool
pIsFirstLine (NAProof 0 Nothing) (SubProof fs _ _) = True
pIsFirstLine (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && pIsFirstLine a (ps !! n)
pIsFirstLine _ _ = False

-- | Returns `True` if the line at `NodeAddr` is a `ProofLine`
pIsLine :: NodeAddr -> Proof -> Bool
pIsLine (NAProof n Nothing) (SubProof _ ps _) = n < L.length ps && isProofLine (ps !! n)
pIsLine (NAProof n (Just a)) (SubProof _ ps _) = n < L.length ps && pIsLine a (ps !! n)
pIsLine _ _ = False

-- | Returns `True` if the line at `NodeAddr` is a conclusion.
pIsConclusion :: NodeAddr -> Proof -> Bool
pIsConclusion NAConclusion _ = True
pIsConclusion (NAProof n (Just a)) (SubProof _ ps _) = n < L.length ps && pIsConclusion a (ps !! n)
pIsConclusion _ _ = False

{- | Returns the line at a given `NodeAddr`.

Returns `Nothing` if the `NodeAddr` does not specify a line of the proof.
-}
pLookup :: NodeAddr -> Proof -> Maybe (Either Assumption Proof)
pLookup (NAAssumption n) (SubProof fs _ _)
  | n < L.length fs = Just . Left $ fs !! n
pLookup (NAProof n Nothing) (SubProof _ ps _)
  | n < L.length ps = Just . Right $ ps !! n
pLookup NAConclusion (SubProof _ ps l) = Just . Right $ ProofLine l
pLookup (NAProof n (Just a)) (SubProof _ ps _)
  | n < L.length ps = pLookup a (ps !! n)
pLookup (NAProof n Nothing) (SubProof _ ps _)
  | n < L.length ps = Just . Right $ ps !! n
pLookup _ _ = Nothing

pIndex :: Int -> Proof -> Maybe (Either Assumption Derivation)
pIndex n p = case fromLineNo n p of
  Nothing -> Nothing
  Just addr -> case pLookup addr p of
    Nothing -> Nothing
    Just (Left a) -> Just (Left a)
    Just (Right (ProofLine d)) -> Just (Right d)
    Just (Right _) -> Nothing

pIndexProof :: Int -> Int -> Proof -> Maybe Proof
pIndexProof start end p = do
  startA <- fromLineNo start p
  endA <- fromLineNo end p
  a1 <- naLevelUp startA
  a2 <- naLevelUp endA
  if pIsFirstFormula startA p
    && pIsConclusion endA p
    && a1 == a2
    then case pLookup a1 p of
      Nothing -> Nothing
      Just (Left{}) -> Nothing
      Just (Right p) -> Just p
    else Nothing

-- TODO use Maybe?
extractFormula :: Either Assumption Derivation -> Formula
extractFormula (Left a) = fromWrapper a
extractFormula (Right (Derivation f _)) = fromWrapper f

extractText :: Either Assumption Derivation -> Text
extractText (Left a) = getText a
extractText (Right (Derivation f _)) = getText f

-- * Updating proof contents

{- | `pUpdateFormula` @f@ @addr@ @proof@ replaces the formula at @addr@ in @proof@ using @f@.

Fails silently
-}
pUpdateFormula :: (Wrapper Formula -> Wrapper Formula) -> NodeAddr -> Proof -> Proof
pUpdateFormula f (NAAssumption n) (SubProof fs ps l) = SubProof (updateAt n f fs) ps l
pUpdateFormula f (NAProof n Nothing) (SubProof fs ps l) | n < L.length ps && isProofLine (ps !! n) = SubProof fs (updateAt n updateProofLine ps) l
 where
  updateProofLine :: Proof -> Proof
  updateProofLine (ProofLine (Derivation formula rule)) = ProofLine (Derivation (f formula) rule)
pUpdateFormula f NAConclusion (SubProof fs ps (Derivation formula rule)) = SubProof fs ps (Derivation (f formula) rule)
pUpdateFormula f (NAProof n (Just addr)) (SubProof fs ps l) | n < L.length ps = SubProof fs (updateAt n (pUpdateFormula f addr) ps) l
pUpdateFormula _ _ p = p

{- | `pUpdateRule` @f@ @addr@ @proof@ replaces the rule at @addr@ in @proof@ using @f@.

Fails silently
-}
pUpdateRule :: (Wrapper RuleApplication -> Wrapper RuleApplication) -> NodeAddr -> Proof -> Proof
pUpdateRule f (NAProof n Nothing) (SubProof fs ps d)
  | n < L.length ps && isProofLine (ps !! n) = SubProof fs (updateAt n (\(ProofLine (Derivation form rule)) -> ProofLine (Derivation form (f rule))) ps) d
pUpdateRule f (NAProof n (Just addr)) (SubProof fs ps d)
  | n < L.length ps && isSubProof (ps !! n) = SubProof fs (updateAt n (pUpdateRule f addr) ps) d
pUpdateRule f NAConclusion (SubProof fs ps (Derivation form rule)) = SubProof fs ps (Derivation form (f rule))
pUpdateRule _ _ p = p

-- * (Re-)moving inside a proof

{- | `pRemove` @addr@ @proof@ removes the element at @addr@ inside @proof@ if it exists (and is not a conclusion).
Otherwise @proof@ is returned.
-}
pRemove :: NodeAddr -> Proof -> Proof
pRemove (NAAssumption n) (SubProof fs ps l) = SubProof (removeAt n fs) ps l
pRemove (NAProof n Nothing) (SubProof fs ps l) | n < L.length ps && isProofLine (ps !! n) = SubProof fs (removeAt n ps) l
pRemove (NAProof n Nothing) (SubProof fs ps l) | n < L.length ps = SubProof fs (removeAt n ps) l
pRemove (NAProof n (Just addr)) (SubProof fs ps l) | n < L.length ps = SubProof fs (updateAt n (pRemove addr) ps) l
pRemove _ p = p

-- | Enumeration for specifying where to insert an element into a proof.
data InsertPosition
  = -- | Insert `Before` the specified address.
    Before
  | -- | Insert `After` the specified address.
    After
  deriving (Show, Eq)

{- | `pInsert` (`Left` @f@) @addr@ @pos@ @proof@ inserts the given formula @f@ at the specified address @addr@ in @proof@.

`pInsert` (`Right` @d@) @addr@ @pos@ @proof@ inserts the given derivation @d@ at the specified address @addr@ in @proof@.

Both formulae and derivations are either inserted `Before` or `After` the specified address.
-}
pInsert :: Either Assumption Proof -> NodeAddr -> InsertPosition -> Proof -> Maybe Proof
pInsert (Left f) (NAAssumption n) pos (SubProof fs ps l)
  | n < L.length fs = case pos of
      Before -> Just $ SubProof (insertAt f n fs) ps l
      After -> Just $ SubProof (insertAt f (n + 1) fs) ps l
pInsert (Left f) (NAProof 0 Nothing) Before (SubProof fs ps l) = Just $ SubProof (insertAt f (L.length fs) fs) ps l
pInsert (Left f) NAConclusion Before (SubProof fs [] l) = Just $ SubProof (insertAt f (L.length fs) fs) [] l
pInsert (Right p) (NAProof n Nothing) pos (SubProof fs ps l)
  | n < L.length ps = case pos of
      Before -> Just $ SubProof fs (insertAt p n ps) l
      After -> Just $ SubProof fs (insertAt p (n + 1) ps) l
pInsert (Right p) NAConclusion Before (SubProof fs ps l) = Just $ SubProof fs (insertAt p (L.length ps) ps) l
pInsert (Right p) (NAAssumption n) After p'@(SubProof fs _ _)
  | n == L.length fs - 1 = pInsert (Right p) (NAProof 0 Nothing) Before p'
pInsert (Right p) (NAProof n (Just (NAAssumption 0))) Before p' = pInsert (Right p) (NAProof n Nothing) Before p'
pInsert (Right p) (NAProof n (Just NAConclusion)) After p' = pInsert (Right p) (NAProof n Nothing) After p'
pInsert e (NAProof n (Just a)) pos (SubProof fs ps l)
  | n < L.length ps && isSubProof (ps !! n) = pInsert e a pos (ps !! n) >>= (\p' -> pure $ SubProof fs (updateAt n (const p') ps) l)
pInsert _ _ _ p = Nothing

{- | `pMove` @target@ @pos@ @source@ @p@ moves the line at the source address
either before or after the target line (depending on @pos@).
-}
pMove :: NodeAddr -> InsertPosition -> NodeAddr -> Proof -> Proof
pMove targetAddr pos sourceAddr p = case (compare targetAddr sourceAddr, pLookup sourceAddr p) of
  (LT, Just node) | not (pIsConclusion sourceAddr p) -> let p' = pRemove sourceAddr p in fromMaybe p $ pInsert node targetAddr pos p'
  (GT, Just node) | not (pIsConclusion sourceAddr p) -> maybe p (pRemove sourceAddr) $ pInsert node targetAddr pos p
  _ -> p

-- * Utilities that are not exported!

{- | `insertAt` @x@ @n@ @xs@ inserts @x@ at index @n@ into @xs@.

Fails for @n < 0@, returns @xs@ for @n > length xs@.
-}
insertAt :: a -> Int -> [a] -> [a]
insertAt x 0 xs = x : xs
insertAt x n [] = []
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