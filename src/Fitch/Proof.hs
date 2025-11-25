module Fitch.Proof where

import Control.Applicative
import Control.Monad.State (evalState)
import Data.List qualified as L
import Data.Maybe

-- * Utilities that are not exported!

insertAt :: a -> Int -> [a] -> [a]
insertAt x 0 xs = x : xs
insertAt x n [] = []
insertAt x n (y : ys) = y : insertAt x (n - 1) ys

removeAt :: Int -> [a] -> [a]
removeAt n [] = []
removeAt n (x : xs)
  | n < 0 = x : xs
  | n == 0 = xs
  | n > 0 = x : removeAt (n - 1) xs

-- | Update nth element of a list, if it exists.
--   @O(min index n)@.
--
--   Precondition: the index is >= 0.
-- (Taken from Agda.Utils.List)
updateAt :: Int -> (a -> a) -> [a] -> [a]
updateAt _ _ [] = []
updateAt 0 f (a : as) = f a : as
updateAt n f (a : as) = a : updateAt (n - 1) f as

data ParseWrapper a where
  Parsed :: String -> a -> ParseWrapper a
  Unparsed :: String -> String -> ParseWrapper a
  deriving (Show, Eq)

data Rule
  = Rule Name [Either Formula Proof] Formula
  deriving (Show, Eq)

type Name = String

data Term
  = Var Name
  | Fun Name [Term]
  deriving (Eq, Ord)

instance Show Term where
  -- TODO verify
  show :: Term -> String
  show (Var v) = v
  show (Fun f []) = f
  show (Fun f ts) = f ++ "(" ++ L.intercalate "," (map show ts)

data Formula
  = Predicate Name [Term]
  | UnaryOp String Formula
  | BinaryOp String Formula Formula
  | Quantifier Name Name Formula
  deriving (Eq, Ord)

instance Show Formula where
  show :: Formula -> String
  show (Predicate p []) = p
  show (Predicate p ts) = p ++ "(" ++ L.intercalate "," (map show ts) ++ ")"
  show (UnaryOp op f) = op ++ "(" ++ show f ++ ")"
  show (BinaryOp op f1 f2) = "(" ++ show f1 ++ ") " ++ op ++ " (" ++ show f2 ++ ")"
  show (Quantifier q v f) = q ++ " " ++ v ++ ". " ++ show f

data Reference where
  -- | Referencing a single line
  LineReference :: Int -> Reference
  -- | Referencing a subproof by a line interval, i.e. `ProofReference` @from@ @to@
  ProofReference :: Int -> Int -> Reference
  deriving (Show, Eq)

type Assumption = ParseWrapper Formula

data RuleApplication
  = RuleApplication Rule [Reference]
  deriving (Show, Eq)

data Derivation
  = Derivation (ParseWrapper Formula) (ParseWrapper RuleApplication)
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
  show = show' 0 0
    where
      withIndent :: Int -> Int -> String -> String
      withIndent line level s = (if line < 0 then "  " else show line ++ replicate ((2 :: Int) - length (show line)) ' ') ++ concat (replicate level "  |") ++ "  |" ++ s ++ "\n"
      showProof :: Int -> Int -> Proof -> String
      showProof line level p@(ProofLine _) = withIndent line level $ show' line level p
      showProof line level p@(SubProof {}) = show' line (level + 1) p
      show' :: Int -> Int -> Proof -> String
      show' line level (ProofLine (Derivation f r)) = show f ++ show r
      show' line level (SubProof fs ps l) = concat fsShow ++ withIndent (-1) level "------" ++ concat psShow ++ conclusionShow
        where
          (line', fsShow) = L.mapAccumL (\ln f -> (ln + 1, withIndent ln level $ show f)) line fs
          (line'', psShow) = L.mapAccumL (\ln' p -> (ln' + lLength p, showProof ln' level p)) line' ps
          conclusionShow = withIndent line'' level (show' line'' level (ProofLine l))

isSubProof :: Proof -> Bool
isSubProof (ProofLine {}) = False
isSubProof (SubProof {}) = True

isProofLine :: Proof -> Bool
isProofLine (ProofLine {}) = True
isProofLine (SubProof {}) = False

-- | The `lLength` of a proof is its number of lines.
lLength :: Proof -> Int
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
fromLineNo :: Int -> Proof -> Maybe NodeAddr
fromLineNo 0 (ProofLine {}) = Just $ NAProof 0 Nothing
fromLineNo n (SubProof [] ps _) = helper n 0 ps
  where
    helper :: Int -> Int -> [Proof] -> Maybe NodeAddr
    helper 0 _ [] = Just NAConclusion
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
fromNodeAddr :: NodeAddr -> Proof -> Maybe Int
fromNodeAddr = go 0
  where
    go :: Int -> NodeAddr -> Proof -> Maybe Int
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
lIsFirstFormula :: NodeAddr -> Proof -> Bool
lIsFirstFormula (NAAssumption 0) (SubProof fs _ _) = True
lIsFirstFormula (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && lIsFirstFormula a (ps !! n)
lIsFirstFormula _ _ = False

lIsFormula :: NodeAddr -> Proof -> Bool
lIsFormula (NAAssumption n) (SubProof fs _ _) = n < L.length fs
lIsFormula (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && lIsFormula a (ps !! n)
lIsFormula _ _ = False

lIsLastFormula :: NodeAddr -> Proof -> Bool
lIsLastFormula (NAAssumption n) (SubProof fs _ _) = n == L.length fs - 1
lIsLastFormula (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && lIsLastFormula a (ps !! n)
lIsLastFormula _ _ = False

lIsFirstLine :: NodeAddr -> Proof -> Bool
lIsFirstLine (NAProof 0 Nothing) (SubProof fs _ _) = True
lIsFirstLine (NAProof n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && lIsFirstLine a (ps !! n)
lIsFirstLine _ _ = False

lIsLine :: NodeAddr -> Proof -> Bool
lIsLine (NAProof n Nothing) (SubProof _ ps _) = n < L.length ps && isProofLine (ps !! n)
lIsLine (NAProof n (Just a)) (SubProof _ ps _) = n < L.length ps && lIsLine a (ps !! n)
lIsLine _ _ = False

lIsConclusion :: NodeAddr -> Proof -> Bool
lIsConclusion NAConclusion _ = True
lIsConclusion (NAProof n (Just a)) (SubProof _ ps _) = n < L.length ps && lIsConclusion a (ps !! n)
lIsConclusion _ _ = False

lLookup :: NodeAddr -> Proof -> Maybe (Either Assumption Proof)
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
lUpdateFormula :: ParseWrapper Formula -> NodeAddr -> Proof -> Proof
lUpdateFormula f (NAAssumption n) (SubProof fs ps l) = SubProof (updateAt n (const f) fs) ps l
lUpdateFormula f (NAProof n Nothing) (SubProof fs ps l) | n < L.length ps && isProofLine (ps !! n) = SubProof fs (updateAt n (updateProofLine f) ps) l
  where
    updateProofLine :: ParseWrapper Formula -> Proof -> Proof
    updateProofLine f (ProofLine (Derivation _ rule)) = ProofLine (Derivation f rule)
lUpdateFormula f NAConclusion (SubProof fs ps (Derivation _ rule)) = SubProof fs ps (Derivation f rule)
lUpdateFormula f (NAProof n (Just addr)) (SubProof fs ps l) | n < L.length ps = SubProof fs (updateAt n (lUpdateFormula f addr) ps) l
lUpdateFormula _ _ p = p

-- * (Re-)moving proofs

-- | `lRemove` @addr@ @proof@ removes the element at @addr@ inside @proof@ if it exists (and is not a conclusion).
-- Otherwise @proof@ is returned.
lRemove :: NodeAddr -> Proof -> Proof
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
lInsert :: Either Assumption Proof -> NodeAddr -> InsertPosition -> Proof -> Maybe Proof
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

lMove :: NodeAddr -> InsertPosition -> NodeAddr -> Proof -> Proof
lMove targetAddr pos sourceAddr p = case (compare targetAddr sourceAddr, lLookup sourceAddr p) of
  (LT, Just node) | not (lIsConclusion sourceAddr p) -> let p' = lRemove sourceAddr p in fromMaybe p $ lInsert node targetAddr pos p'
  (GT, Just node) | not (lIsConclusion sourceAddr p) -> maybe p (lRemove sourceAddr) $ lInsert node targetAddr pos p
  _ -> p