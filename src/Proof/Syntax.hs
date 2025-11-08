module Proof.Syntax where

import Control.Applicative
import qualified Data.List as L
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
  -- | A single line of the prove consisting of a derivation.
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
-- * a single line or proof inside the proof `NAProof` @n@ `Nothing`
-- * a reference to a nested element inside a subproof `NAProof` @n@ (`Just` @a@)
-- TODO cases for NAProof n Nothing everywhere!!
data NodeAddr
  = NAAssumption Int
  | NALine Int
  | NAProof Int (Maybe NodeAddr)
  deriving (Show, Eq)

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
  compare (NAProof n (Just addr1)) (NAProof m (Just addr2)) | n == m = compare addr1 addr2
  compare (NAProof n _) (NAProof m _) = compare n m

-- ** Conversion between line numbers and `NodeAddr`

-- | Takes a line index and returns the corresponding `NodeAddr` for a given proof.
fromLineNo :: Int -> Proof formula rule -> Maybe NodeAddr
fromLineNo 0 (ProofLine {}) = Just $ NALine 0
fromLineNo 0 (SubProof [] [] _) = Just $ NALine 0
fromLineNo n (SubProof [] [] _) = Nothing
fromLineNo n (SubProof [] ps _) = helper n 0 ps
  where
    helper :: Int -> Int -> [Proof formula rule] -> Maybe NodeAddr
    helper n m [] = Nothing
    helper 0 m ((ProofLine {}) : ps) = Just $ NALine m
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
    go 0 (NALine 0) (ProofLine {}) = Just 0
    go n (NAAssumption m) (SubProof fs _ _) | m < L.length fs = return $ n + m
    go n (NAAssumption m) (SubProof fs _ _) = Nothing
    go 0 (NALine 0) (SubProof [] [] _) = Just 0
    go n (NALine m) (SubProof fs ps _) | m < L.length ps && isProofLine (ps !! m) = return $ L.length fs + n + foldr (\p n -> n + lLength p) 0 (take m ps)
    go n (NALine m) (SubProof fs ps _) | m == L.length ps = return $ L.length fs + n + foldr (\p n -> n + lLength p) 0 ps
    go n (NAProof m (Just addr)) (SubProof fs ps _) | m < L.length ps && isSubProof (ps !! m) = go (L.length fs + n + foldr (\p n -> n + lLength p) 0 (take m ps)) addr (ps !! m)
    go _ _ _ = Nothing

-- ** Utilities for working with addresses

naAppendAssumption :: Int -> NodeAddr -> NodeAddr
naAppendAssumption m (NAProof n (Just a)) = NAProof n (Just $ naAppendAssumption m a)
naAppendAssumption m (NAProof n Nothing) = NAProof n (Just $ NAAssumption m)
naAppendAssumption m a = error $ show a ++ "\n cannot append assumption."

naAppendLine :: Int -> NodeAddr -> NodeAddr
naAppendLine m (NAProof n (Just a)) = NAProof n (Just $ naAppendLine m a)
naAppendLine m (NAProof n Nothing) = NAProof n (Just $ NALine m)
naAppendLine m a = error $ show a ++ "\n cannot append assumption."

-- | `incrementNodeAddr` increments an address by 1, while keeping the nesting structure unchanged.
incrementNodeAddr :: NodeAddr -> NodeAddr
incrementNodeAddr (NAAssumption n) = NAAssumption (n + 1)
incrementNodeAddr (NALine n) = NALine (n + 1)
incrementNodeAddr (NAProof n (Just a)) = NAProof n (Just (incrementNodeAddr a))

-- * Querying proofs

-- TODO remove all `l` prefixes!

lIsFormula :: NodeAddr -> Proof formula rule -> Bool
lIsFormula (NAAssumption n) (SubProof fs _ _) = n < L.length fs
lIsFormula (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && lIsFormula a (ps !! n)
lIsFormula _ _ = False

lIsLine :: NodeAddr -> Proof formula rule -> Bool
lIsLine (NALine n) (SubProof _ ps _) = n < L.length ps && isProofLine (ps !! n)
lIsLine (NAProof n (Just a)) (SubProof _ ps _) = n < L.length ps && lIsLine a (ps !! n)
lIsLine _ _ = False

lLookup :: NodeAddr -> Proof formula rule -> Maybe (Either (Assumption formula) (Derivation formula rule))
lLookup (NAAssumption n) (SubProof fs _ _)
  | n < L.length fs = Just . Left $ fs !! n
lLookup (NALine n) (SubProof _ ps _)
  | n < L.length ps = case ps !! n of
      ProofLine d -> Just $ Right d
      SubProof {} -> Nothing
lLookup (NALine n) (SubProof _ ps l)
  | n == L.length ps = Just $ Right l
lLookup (NAProof n (Just a)) (SubProof _ ps _)
  | n < L.length ps = lLookup a (ps !! n)
lLookup _ _ = Nothing

-- * Updating proof contents

-- | `lUpdateFormula` @f@ @addr@ @proof@ replaces the formula at @addr@ in @proof@ with @f@.
--
-- Fails silently
lUpdateFormula :: forall formula rule. formula -> NodeAddr -> Proof formula rule -> Proof formula rule
lUpdateFormula f (NAAssumption n) (SubProof fs ps l) = SubProof (updateAt n (const f) fs) ps l
lUpdateFormula f (NALine n) (SubProof fs ps l) | n < L.length ps && isProofLine (ps !! n) = SubProof fs (updateAt n (updateProofLine f) ps) l
  where
    updateProofLine :: formula -> Proof formula rule -> Proof formula rule
    updateProofLine f (ProofLine (Derivation _ rule ref)) = ProofLine (Derivation f rule ref)
lUpdateFormula f (NALine n) (SubProof fs ps (Derivation _ rule ref)) | n == L.length ps = SubProof fs ps (Derivation f rule ref)
lUpdateFormula f (NAProof n (Just addr)) (SubProof fs ps l) | n < L.length ps = SubProof fs (updateAt n (lUpdateFormula f addr) ps) l
lUpdateFormula _ _ p = p

-- * (Re-)moving proofs

-- | `lRemove` @addr@ @proof@ removes the element at @addr@ inside @proof@ if it exists (and is not a conclusion).
-- Otherwise @proof@ is returned.
lRemove :: NodeAddr -> Proof formula rule -> Proof formula rule
lRemove (NAAssumption n) (SubProof fs ps l) = SubProof (removeAt n fs) ps l
lRemove (NALine n) (SubProof fs ps l) | n < L.length ps && isProofLine (ps !! n) = SubProof fs (removeAt n ps) l
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
-- TODO can insert `Before` conclusion??
lInsert :: Either (Assumption formula) (Derivation formula rule) -> NodeAddr -> InsertPosition -> Proof formula rule -> Proof formula rule
lInsert (Left f) (NAAssumption n) pos (SubProof fs ps l)
  | n < L.length fs = case pos of
      Before -> SubProof (insertAt f n fs) ps l
      After -> SubProof (insertAt f (n + 1) fs) ps l
lInsert (Right d) (NALine n) pos (SubProof fs ps l)
  | n < L.length ps = case pos of
      Before -> SubProof fs (insertAt (ProofLine d) n ps) l
      After -> SubProof fs (insertAt (ProofLine d) (n + 1) ps) l
lInsert e (NAProof n (Just a)) pos (SubProof fs ps l)
  | n < L.length ps && isSubProof (ps !! n) = SubProof fs (updateAt n (lInsert e a pos) ps) l
lInsert _ _ _ p = p