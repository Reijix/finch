module Proof.Syntax where

import Control.Applicative
import Data.List qualified as L
import Data.Maybe
import Proof.Util

data RuleSpec formula rule = RuleSpec rule [Either formula (Proof formula rule)] formula deriving (Show, Eq)

data Reference where
  -- | Referencing a single line
  LineReference :: Int -> Reference
  -- | Referencing a subproof
  ProofReference :: Int -> Int -> Reference
  deriving (Show, Eq)

type Assumption formula = formula

data Derivation formula rule = Derivation formula rule [Reference] deriving (Show, Eq)

-- | A datatype for respresenting fitch-style proofs.
data Proof formula rule where
  -- | A single line of the proof consisting of a derivation.
  ProofLine :: Derivation formula rule -> Proof formula rule
  -- | A subproof consisting of a list of assumptions, a list of subproofs (or derivations) and a conclusion.
  SubProof :: [Assumption formula] -> [Proof formula rule] -> Derivation formula rule -> Proof formula rule
  deriving (Eq)

instance (Show formula, Show rule) => Show (Proof formula rule) where
  show :: (Show formula, Show rule) => Proof formula rule -> String
  show = show' 0 0
    where
      withIndent :: Int -> Int -> String -> String
      withIndent line level s = (if line < 0 then "  " else show line ++ replicate ((2 :: Int) - length (show line)) ' ') ++ concat (replicate level "  |") ++ "  |" ++ s ++ "\n"
      showProof :: Int -> Int -> Proof formula rule -> String
      showProof line level p@(ProofLine _) = withIndent line level $ show' line level p
      showProof line level p@(SubProof {}) = show' line (level + 1) p
      show' :: Int -> Int -> Proof formula rule -> String
      show' line level (ProofLine (Derivation f r _)) = show f ++ show r
      show' line level (SubProof fs ps l) = concat fsShow ++ withIndent (-1) level "------" ++ concat psShow ++ conclusionShow
        where
          (line', fsShow) = L.mapAccumL (\ln f -> (ln + 1, withIndent ln level $ show f)) line fs
          (line'', psShow) = L.mapAccumL (\ln' p -> (ln' + lLength p, showProof ln' level p)) line' ps
          conclusionShow = withIndent line'' level (show' line'' level (ProofLine l))

isSubProof :: Proof formula rule -> Bool
isSubProof (ProofLine {}) = False
isSubProof (SubProof {}) = True

isProofLine :: Proof formula rule -> Bool
isProofLine (ProofLine {}) = True
isProofLine (SubProof {}) = False

-- | The `lLength` of a proof is its number of lines.
lLength :: Proof formula rule -> Int
lLength (ProofLine l) = 1
lLength (SubProof fs ps _) = foldr (\p n -> lLength p + n) (L.length fs + 1) ps

-- * Indexing proofs

-- | This type is used for indexing lines in a proof.
--   Its recursive structure makes defining functions that manipulate proofs more convenient
--
-- ==== Usage
--
-- A `NodeAddr` may either be a reference to
-- * a single assumption `NAAssumption` @n@,
-- * the conclusion `NAConclusion` of the proof
-- * a single proof or line inside the proof `NAProof` @n@ `Nothing`
-- * a reference to a nested element inside a subproof `NAProof` @n@ (`Just` @a@)
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

-- | Takes a line index and returns the corresponding `NodeAddr` for a given proof.
fromLineNo :: Int -> Proof formula rule -> Maybe NodeAddr
fromLineNo 0 (ProofLine {}) = Just $ NAProof 0 Nothing
-- fromLineNo 0 (SubProof [] [] _) = Just NAConclusion
-- fromLineNo n (SubProof [] [] _) = Nothing
-- TODO handle conclusion
fromLineNo n (SubProof [] ps _) = helper n 0 ps
  where
    helper :: Int -> Int -> [Proof formula rule] -> Maybe NodeAddr
    helper n m [] = Nothing
    helper 0 m ((ProofLine {}) : ps) = Just $ NAProof m Nothing
    helper n m (p : ps) | n < lLength p = do
      addr <- fromLineNo n p
      return $ NAProof m (Just addr)
    helper n m (p : ps) = helper (n - lLength p) (m + 1) ps
fromLineNo n (SubProof fs _ _) | n < L.length fs = Just $ NAAssumption n
fromLineNo n (SubProof fs ps l) = fromLineNo (n - L.length fs) (SubProof [] ps l)
fromLineNo n p = Nothing

-- | Takes a `NodeAddr` and returns the corresponding line index for a given proof.
fromNodeAddr :: NodeAddr -> Proof formula rule -> Maybe Int
fromNodeAddr = go 0
  where
    go :: Int -> NodeAddr -> Proof formula rule -> Maybe Int
    go 0 (NAProof 0 Nothing) (ProofLine {}) = Just 0
    go n (NAAssumption m) (SubProof fs _ _) | m < L.length fs = return $ n + m
    go n (NAAssumption m) (SubProof fs _ _) = Nothing
    go 0 (NAProof 0 Nothing) (SubProof [] [] _) = Just 0
    go n (NAProof m Nothing) (SubProof fs ps _) | m < L.length ps && isProofLine (ps !! m) = return $ L.length fs + n + foldr (\p n -> n + lLength p) 0 (take m ps)
    go n NAConclusion (SubProof fs ps _) = return $ L.length fs + n + foldr (\p n -> n + lLength p) 0 ps
    go n (NAProof m (Just addr)) (SubProof fs ps _) | m < L.length ps && isSubProof (ps !! m) = go (L.length fs + n + foldr (\p n -> n + lLength p) 0 (take m ps)) addr (ps !! m)
    go _ _ _ = Nothing

-- ** Utilities for working with addresses

naAppendAssumption :: Int -> NodeAddr -> NodeAddr
naAppendAssumption m (NAProof n (Just a)) = NAProof n (Just $ naAppendAssumption m a)
naAppendAssumption m (NAProof n Nothing) = NAProof n (Just $ NAAssumption m)
naAppendAssumption m a = error $ show a ++ "\n cannot append assumption."

naAppendProof :: Int -> NodeAddr -> NodeAddr
naAppendProof m (NAProof n (Just a)) = NAProof n (Just $ naAppendProof m a)
naAppendProof m (NAProof n Nothing) = NAProof n (Just $ NAProof m Nothing)
naAppendProof m a = error $ show a ++ "\n cannot append line."

naAppendConclusion :: NodeAddr -> NodeAddr
naAppendConclusion (NAProof n (Just a)) = NAProof n (Just $ naAppendConclusion a)
naAppendConclusion (NAProof n Nothing) = NAProof n (Just NAConclusion)
naAppendConclusion a = error $ show a ++ "\n cannot append conclusion."

-- | `incrementNodeAddr` increments an address by 1, while keeping the nesting structure unchanged.
incrementNodeAddr :: NodeAddr -> NodeAddr
incrementNodeAddr (NAAssumption n) = NAAssumption (n + 1)
incrementNodeAddr (NAProof n Nothing) = NAProof (n + 1) Nothing
incrementNodeAddr (NAProof n (Just a)) = NAProof n (Just (incrementNodeAddr a))

-- * Querying proofs

-- TODO remove all `l` prefixes!
lIsFirstFormula :: NodeAddr -> Proof formula rule -> Bool
lIsFirstFormula (NAAssumption 0) (SubProof fs _ _) = True
lIsFirstFormula (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && lIsFirstFormula a (ps !! n)
lIsFirstFormula _ _ = False

lIsFormula :: NodeAddr -> Proof formula rule -> Bool
lIsFormula (NAAssumption n) (SubProof fs _ _) = n < L.length fs
lIsFormula (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && lIsFormula a (ps !! n)
lIsFormula _ _ = False

lIsLastFormula :: NodeAddr -> Proof formula rule -> Bool
lIsLastFormula (NAAssumption n) (SubProof fs _ _) = n == L.length fs - 1
lIsLastFormula (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && lIsLastFormula a (ps !! n)
lIsLastFormula _ _ = False

lIsFirstLine :: NodeAddr -> Proof formula rule -> Bool
lIsFirstLine (NAProof 0 Nothing) (SubProof fs _ _) = True
lIsFirstLine (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && lIsFirstLine a (ps !! n)
lIsFirstLine _ _ = False

lIsLine :: NodeAddr -> Proof formula rule -> Bool
lIsLine (NAProof n Nothing) (SubProof _ ps _) = n < L.length ps && isProofLine (ps !! n)
lIsLine (NAProof n (Just a)) (SubProof _ ps _) = n < L.length ps && lIsLine a (ps !! n)
lIsLine _ _ = False

lIsConclusion :: NodeAddr -> Proof formula rule -> Bool
lIsConclusion NAConclusion _ = True
lIsConclusion (NAProof n (Just a)) (SubProof _ ps _) = n < L.length ps && lIsConclusion a (ps !! n)
lIsConclusion _ _ = False

lLookup :: NodeAddr -> Proof formula rule -> Maybe (Either (Assumption formula) (Proof formula rule))
lLookup (NAAssumption n) (SubProof fs _ _)
  | n < L.length fs = Just . Left $ fs !! n
lLookup (NAProof n Nothing) (SubProof _ ps _)
  | n < L.length ps = Just . Right $ ps !! n
lLookup NAConclusion (SubProof _ ps l) = Just . Right $ ProofLine l
lLookup (NAProof n (Just a)) (SubProof _ ps _)
  | n < L.length ps = lLookup a (ps !! n)
lLookup (NAProof n Nothing) (SubProof _ ps _)
  | n < L.length ps = Just . Right $ ps !! n
lLookup _ _ = Nothing

-- * Updating proof contents

-- | `lUpdateFormula` @f@ @addr@ @proof@ replaces the formula at @addr@ in @proof@ with @f@.
--
-- Fails silently
lUpdateFormula :: forall formula rule. formula -> NodeAddr -> Proof formula rule -> Proof formula rule
lUpdateFormula f (NAAssumption n) (SubProof fs ps l) = SubProof (updateAt n (const f) fs) ps l
lUpdateFormula f (NAProof n Nothing) (SubProof fs ps l) | n < L.length ps && isProofLine (ps !! n) = SubProof fs (updateAt n (updateProofLine f) ps) l
  where
    updateProofLine :: formula -> Proof formula rule -> Proof formula rule
    updateProofLine f (ProofLine (Derivation _ rule ref)) = ProofLine (Derivation f rule ref)
lUpdateFormula f NAConclusion (SubProof fs ps (Derivation _ rule ref)) = SubProof fs ps (Derivation f rule ref)
lUpdateFormula f (NAProof n (Just addr)) (SubProof fs ps l) | n < L.length ps = SubProof fs (updateAt n (lUpdateFormula f addr) ps) l
lUpdateFormula _ _ p = p

-- * (Re-)moving proofs

-- | `lRemove` @addr@ @proof@ removes the element at @addr@ inside @proof@ if it exists (and is not a conclusion).
-- Otherwise @proof@ is returned.
lRemove :: NodeAddr -> Proof formula rule -> Proof formula rule
lRemove (NAAssumption n) (SubProof fs ps l) = SubProof (removeAt n fs) ps l
lRemove (NAProof n Nothing) (SubProof fs ps l) | n < L.length ps && isProofLine (ps !! n) = SubProof fs (removeAt n ps) l
lRemove (NAProof n Nothing) (SubProof fs ps l) | n < L.length ps = SubProof fs (removeAt n ps) l
lRemove (NAProof n (Just addr)) (SubProof fs ps l) | n < L.length ps = SubProof fs (updateAt n (lRemove addr) ps) l
lRemove _ p = p

-- | Enumeration for specifying where to insert an element into a proof.
data InsertPosition
  = -- | Insert `Before` the specified address.
    Before
  | -- | Insert `After` the specified address.
    After
  deriving (Show, Eq)

-- | `lInsert` (`Left` @f@) @addr@ @pos@ @proof@ inserts the given formula @f@ at the specified address @addr@ in @proof@.
--
-- `lInsert` (`Right` @d@) @addr@ @pos@ @proof@ inserts the given derivation @d@ at the specified address @addr@ in @proof@.
--
-- Both formulae and derivations are either inserted `Before` or `After` the specified address.
lInsert :: Either (Assumption formula) (Proof formula rule) -> NodeAddr -> InsertPosition -> Proof formula rule -> Maybe (Proof formula rule)
lInsert (Left f) (NAAssumption n) pos (SubProof fs ps l)
  | n < L.length fs = case pos of
      Before -> Just $ SubProof (insertAt f n fs) ps l
      After -> Just $ SubProof (insertAt f (n + 1) fs) ps l
lInsert (Left f) (NAProof 0 Nothing) Before (SubProof fs ps l) = Just $ SubProof (insertAt f (L.length fs) fs) ps l
lInsert (Left f) NAConclusion Before (SubProof fs [] l) = Just $ SubProof (insertAt f (L.length fs) fs) [] l
lInsert (Right p) (NAProof n Nothing) pos (SubProof fs ps l)
  | n < L.length ps = case pos of
      Before -> Just $ SubProof fs (insertAt p n ps) l
      After -> Just $ SubProof fs (insertAt p (n + 1) ps) l
lInsert (Right p) NAConclusion Before (SubProof fs ps l) = Just $ SubProof fs (insertAt p (L.length ps) ps) l
lInsert (Right p) (NAAssumption n) After p'@(SubProof fs _ _)
  | n == L.length fs - 1 = lInsert (Right p) (NAProof 0 Nothing) Before p'
lInsert (Right p) (NAProof n (Just (NAAssumption 0))) Before p' = lInsert (Right p) (NAProof n Nothing) Before p'
lInsert (Right p) (NAProof n (Just NAConclusion)) After p' = lInsert (Right p) (NAProof n Nothing) After p'
lInsert e (NAProof n (Just a)) pos (SubProof fs ps l)
  | n < L.length ps && isSubProof (ps !! n) = lInsert e a pos (ps !! n) >>= (\p' -> pure $ SubProof fs (updateAt n (const p') ps) l)
lInsert _ _ _ p = Nothing

lMove :: NodeAddr -> InsertPosition -> NodeAddr -> Proof formula rule -> Proof formula rule
lMove targetAddr pos sourceAddr p = case lLookup sourceAddr p of
  Nothing -> p
  Just node -> case compare targetAddr sourceAddr of
    LT -> let p' = lRemove sourceAddr p in fromMaybe p $ lInsert node targetAddr pos p'
    GT -> maybe p (lRemove sourceAddr) $ lInsert node targetAddr pos p
    _ -> p