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

fromLineNo :: Int -> Proof formula rule -> Maybe LineAddr
fromLineNo 0 (ProofLine {}) = Just $ LADeriv 0 Nothing
fromLineNo n (SubProof [] [] _) = Nothing
fromLineNo n (SubProof [] ps _) = helper n 0 ps
  where
    helper :: Int -> Int -> [Proof formula rule] -> Maybe LineAddr
    helper n m [] = Nothing
    helper 0 m ((ProofLine {}) : ps) = Just $ LADeriv m Nothing
    helper n m (p : ps) | n < lLength p = do
      addr <- fromLineNo n p
      return $ LADeriv m (Just addr)
    helper n m (p : ps) = helper (n - lLength p) (m + 1) ps
fromLineNo n (SubProof fs _ _) | n < L.length fs = Just $ LAAssumption n
fromLineNo n (SubProof fs ps l) = fromLineNo (n - L.length fs) (SubProof [] ps l)
fromLineNo n p = Nothing

fromLineAddr :: LineAddr -> Proof formula rule -> Maybe Int
fromLineAddr = go 0
  where
    go :: Int -> LineAddr -> Proof formula rule -> Maybe Int
    go 0 (LADeriv 0 Nothing) (ProofLine {}) = Just 0
    go n addr (ProofLine {}) = Nothing
    go n (LAAssumption m) (SubProof fs _ _) | m < L.length fs = return $ n + m
    go n (LAAssumption m) (SubProof fs _ _) = Nothing
    go n (LADeriv m Nothing) (SubProof fs ps _) | m < L.length ps && isProofLine (ps !! m) = return $ L.length fs + n + foldr (\p n -> n + lLength p) 0 (take m ps)
    go n (LADeriv m (Just addr)) (SubProof fs ps _) | m < L.length ps && isSubProof (ps !! m) = go (L.length fs + n + foldr (\p n -> n + lLength p) 0 (take m ps)) addr (ps !! m)

data LineAddr = LAAssumption Int | LADeriv Int (Maybe LineAddr) deriving (Show, Eq)

incrementLineAddr :: LineAddr -> LineAddr
incrementLineAddr (LAAssumption n) = LAAssumption $ n + 1
incrementLineAddr (LADeriv n Nothing) = LADeriv (n + 1) Nothing
incrementLineAddr (LADeriv n (Just a)) = LADeriv n (Just (incrementLineAddr a))

-- TODO implement corresponding functions
data ProofAddr = ProofAddr Int (Maybe ProofAddr)

-- TODO improve
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

lLookupAddr :: LineAddr -> Proof formula rule -> Maybe (Either (Assumption formula) (Derivation formula rule))
lLookupAddr (LAAssumption n) (SubProof fs _ _)
  | n < L.length fs = Just . Left $ fs !! n
lLookupAddr (LADeriv n Nothing) (SubProof _ ps _)
  | n < L.length ps = case ps !! n of
      ProofLine d -> Just $ Right d
      SubProof {} -> Nothing
lLookupAddr (LADeriv n (Just a)) (SubProof _ ps _)
  | n < L.length ps = lLookupAddr a (ps !! n)

lRemoveAddr :: LineAddr -> Proof formula rule -> Proof formula rule
lRemoveAddr (LAAssumption n) (SubProof fs ps l) = SubProof (removeAt n fs) ps l
lRemoveAddr (LADeriv n Nothing) (SubProof fs ps l) | n < L.length ps && isProofLine (ps !! n) = SubProof fs (removeAt n ps) l
lRemoveAddr (LADeriv n (Just addr)) (SubProof fs ps l) | n < L.length ps = SubProof fs (updateAt n (lRemoveAddr addr) ps) l
lRemoveAddr _ p = p

data InsertPosition = Before | After

lInsertAddr :: Either (Assumption formula) (Derivation formula rule) -> LineAddr -> InsertPosition -> Proof formula rule -> Proof formula rule
lInsertAddr (Left f) (LAAssumption n) pos (SubProof fs ps l)
  | n < L.length fs = case pos of
      Before -> SubProof (insertAt f n fs) ps l
      After -> SubProof (insertAt f (n + 1) fs) ps l
lInsertAddr (Right d) (LADeriv n Nothing) pos (SubProof fs ps l)
  | n < L.length ps = case pos of
      Before -> SubProof fs (insertAt (ProofLine d) n ps) l
      After -> SubProof fs (insertAt (ProofLine d) (n + 1) ps) l
lInsertAddr e (LADeriv n (Just a)) pos (SubProof fs ps l)
  | n < L.length ps && isSubProof (ps !! n) = SubProof fs (updateAt n (lInsertAddr e a pos) ps) l
lInsertAddr _ _ _ p = p

lIsFormulaAddr :: LineAddr -> Proof formula rule -> Bool
lIsFormulaAddr (LAAssumption n) (SubProof fs _ _) = n < L.length fs
lIsFormulaAddr (LADeriv n (Just a)) (SubProof _ ps _) =
  n < L.length ps && isSubProof (ps !! n) && lIsFormulaAddr a (ps !! n)
lIsFormulaAddr _ _ = False

lIsLineAddr :: LineAddr -> Proof formula rule -> Bool
lIsLineAddr (LADeriv n Nothing) (SubProof _ ps _) = n < L.length ps && isProofLine (ps !! n)
lIsLineAddr (LADeriv n (Just a)) (SubProof _ ps _) = n < L.length ps && lIsLineAddr a (ps !! n)
lIsLineAddr _ _ = False