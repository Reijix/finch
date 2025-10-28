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

data Proof formula rule where
  ProofLine :: Derivation formula rule -> Proof formula rule
  SubProof :: [Assumption formula] -> [Proof formula rule] -> Derivation formula rule -> Proof formula rule
  deriving (Eq)

isSubProof :: Proof formula rule -> Bool
isSubProof (ProofLine {}) = False
isSubProof (SubProof {}) = True

isProofLine :: Proof formula rule -> Bool
isProofLine (ProofLine {}) = True
isProofLine (SubProof {}) = False

lineNoToLineAddr :: Int -> Proof formula rule -> Maybe LineAddr
lineNoToLineAddr 0 (ProofLine {}) = Just $ LADeriv 0 Nothing
lineNoToLineAddr n (SubProof [] [] _) = Nothing
lineNoToLineAddr n (SubProof [] ps _) = helper n 0 ps
  where
    helper :: Int -> Int -> [Proof formula rule] -> Maybe LineAddr
    helper n m [] = Nothing
    helper 0 m ((ProofLine {}) : ps) = Just $ LADeriv m Nothing
    helper n m (p : ps) | n < lLength p = do
      addr <- lineNoToLineAddr n p
      return $ LADeriv m (Just addr)
    helper n m (p : ps) = helper (n - lLength p) (m + 1) ps
lineNoToLineAddr n (SubProof fs _ _) | n < L.length fs = Just $ LAAssumption n
lineNoToLineAddr n (SubProof fs ps l) = lineNoToLineAddr (n - L.length fs) (SubProof [] ps l)

lineAddrToLineNo :: LineAddr -> Proof formula rule -> Maybe Int
lineAddrToLineNo = go 0
  where
    go :: Int -> LineAddr -> Proof formula rule -> Maybe Int
    go n addr (ProofLine {}) = Nothing
    go n (LAAssumption m) (SubProof fs _ _) | m < L.length fs = return $ n + m
    go n (LAAssumption m) (SubProof fs _ _) = Nothing
    go n (LADeriv m Nothing) (SubProof fs ps _) | m < L.length ps && isProofLine (ps !! m) = return $ L.length fs + n + m
    go n (LADeriv m (Just addr)) (SubProof fs ps _) | m < L.length ps && isSubProof (ps !! m) = go (L.length fs + n + m) addr (ps !! m)

data LineAddr = LAAssumption Int | LADeriv Int (Maybe LineAddr) deriving (Show, Eq)

data ProofAddr = ProofAddr Int (Maybe ProofAddr)

instance (Show formula, Show rule) => Show (Proof formula rule) where
  show :: (Show formula, Show rule) => Proof formula rule -> String
  show = show' 0
    where
      withSpaces :: Int -> String -> String
      withSpaces n s = replicate n ' ' ++ s ++ "\n"
      show' :: Int -> Proof formula rule -> String
      show' n (ProofLine (Derivation f r _)) = show f ++ show r
      show' n (SubProof fs ps l) = concatMap (withSpaces n . show) fs ++ concatMap (showProof n) ps ++ withSpaces n (show' n (ProofLine l))
        where
          showProof :: Int -> Proof formula rule -> String
          showProof n p@(ProofLine _) = withSpaces n $ show' n p
          showProof n p@(SubProof {}) = show' (n + 2) p

lLength :: Proof formula rule -> Int
lLength (ProofLine l) = 1
lLength (SubProof fs ps _) = foldr (\p n -> lLength p + n) (L.length fs + 1) ps

lLookup :: Proof formula rule -> Int -> Maybe (Either (Assumption formula) (Derivation formula rule))
lLookup (ProofLine d) 0 = Just $ Right d
lLookup (ProofLine _) _ = Nothing
lLookup (SubProof [] [] l) 0 = Just $ Right l
lLookup (SubProof [] [] _) _ = Nothing
lLookup (SubProof [] (p : _) _) n | n < lLength p = lLookup p n
lLookup (SubProof [] (p : ps) l) n = lLookup (SubProof [] ps l) (n - lLength p)
lLookup (SubProof fs ps l) n = if n < L.length fs then Just . Left $ fs L.!! n else lLookup (SubProof [] ps l) (n - L.length fs)

-- | returns whether a given line of a proof is movable (always returns true, except for conclusions, aka the last line in a proof.)
lIsMovable :: Int -> Proof formula rule -> Bool
lIsMovable n _ | n < 0 = False
lIsMovable n (ProofLine _) = False
lIsMovable _ (SubProof [] [] _) = False
lIsMovable 0 (SubProof [] ((ProofLine {}) : ps) _) = True
lIsMovable n (SubProof [] (p : ps) _) | n < lLength p = lIsMovable n p
lIsMovable n (SubProof [] (p : ps) l) = lIsMovable (n - lLength p) (SubProof [] ps l)
lIsMovable n (SubProof fs ps l) = lIsMovable (n - L.length fs) (SubProof [] ps l)

lRemoveAddr :: LineAddr -> Proof formula rule -> Proof formula rule
lRemoveAddr (LAAssumption n) (SubProof fs ps l) = SubProof (removeAt n fs) ps l
lRemoveAddr addr@(LADeriv n Nothing) p@(SubProof fs ps l) | n < L.length ps && isSubProof (ps !! n) = SubProof fs (removeAt n ps) l
lRemoveAddr (LADeriv n (Just addr)) (SubProof fs ps l) = SubProof fs (updateAt n (lRemoveAddr addr) ps) l
lRemoveAddr _ p = p

lRemove :: Int -> Proof formula rule -> Proof formula rule
lRemove n p | n < 0 = p
lRemove n p@(ProofLine {}) = p
lRemove n p@(SubProof [] [] _) = p
lRemove 0 (SubProof [] (ProofLine {} : ps) l) = SubProof [] ps l
lRemove n (SubProof [] (p : ps) l) | n < lLength p = SubProof [] (lRemove n p : ps) l
lRemove n (SubProof [] (p : ps) l) = case lRemove (n - lLength p) (SubProof [] ps l) of
  (SubProof [] ps' _) -> SubProof [] (p : ps') l
lRemove n (SubProof fs ps l) | n < L.length fs = SubProof (removeAt n fs) ps l
lRemove n (SubProof fs ps l) = case lRemove (n - L.length fs) (SubProof [] ps l) of
  (SubProof [] ps' _) -> SubProof fs ps' l

data InsertPosition = Before | After

lInsert :: Either (Assumption formula) (Derivation formula rule) -> Int -> InsertPosition -> Proof formula rule -> Proof formula rule
lInsert _ n _ p | n < 0 = p
lInsert _ n _ p@(ProofLine _) = p
lInsert (Right d) 0 Before (SubProof [] (p@(ProofLine {}) : ps) l) = SubProof [] (ProofLine d : p : ps) l
lInsert (Right d) 0 After (SubProof [] (p@(ProofLine {}) : ps) l) = SubProof [] (p : ProofLine d : ps) l
lInsert (Right d) 0 pos (SubProof [] (p : ps) l) = SubProof [] (lInsert (Right d) 0 pos p : ps) l
lInsert l n pos (SubProof [] (p : ps) d) | n < lLength p = SubProof [] (lInsert l n pos p : ps) d
lInsert l n pos (SubProof [] (p : ps) d) = case lInsert l (n - lLength p) pos (SubProof [] ps d) of
  (SubProof fs' ps' _) -> SubProof fs' (p : ps') d
lInsert (Left a) n pos (SubProof fs ps d) | n < L.length fs = case pos of
  Before -> SubProof (insertAt a n fs) ps d
  After -> SubProof (insertAt a (n + 1) fs) ps d
lInsert (Left a) n pos p@(SubProof [] [] _) = p
lInsert l n pos (SubProof fs ps d) = case lInsert l (n - L.length fs) pos (SubProof [] ps d) of
  (SubProof _ ps' _) -> SubProof fs ps' d

lIsFormula :: Int -> Proof formula rule -> Bool
lIsFormula n p | n < 0 = False
lIsFormula n (ProofLine _) = False
lIsFormula n (SubProof [] [] d) = False
lIsFormula n (SubProof [] (p : ps) d) = lIsFormula n p || lIsFormula (n - lLength p) (SubProof [] ps d)
lIsFormula n (SubProof fs ps _) | n < L.length fs = True
lIsFormula n (SubProof fs ps d) = lIsFormula (n - L.length fs) (SubProof [] ps d)

lIsLine :: Int -> Proof formula rule -> Bool
lIsLine n p | n < 0 = False
lIsLine n (ProofLine _) = False
lIsLine n (SubProof [] [] d) = False
lIsLine 0 (SubProof [] (ProofLine {} : ps) d) = True
lIsLine n (SubProof [] (p : ps) d) | n < lLength p = lIsLine n p
lIsLine n (SubProof [] (p : ps) d) = lIsLine (n - lLength p) (SubProof [] ps d)
lIsLine n (SubProof fs ps d) = lIsLine (n - L.length fs) (SubProof [] ps d)