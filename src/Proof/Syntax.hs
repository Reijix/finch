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

lLookup :: Proof formula rule -> Int -> Either (Assumption formula) (Derivation formula rule)
lLookup (ProofLine d) 0 = Right d
lLookup (ProofLine _) _ = error "Tried (!!) on ProofLine with n > 0"
lLookup (SubProof [] [] l) 0 = Right l
lLookup (SubProof [] [] _) _ = error "Tried (!!) on SubProof [] [] l with n > 0"
lLookup (SubProof [] (p : _) _) n | n < lLength p = lLookup p n
lLookup (SubProof [] (_ : ps) l) n = lLookup (SubProof [] ps l) n
lLookup (SubProof fs ps l) n = if n < L.length fs then Left $ fs L.!! n else lLookup (SubProof [] ps l) (n - L.length fs)

-- | returns whether a given line of a proof is movable (always returns true, except for conclusions, aka the last line in a proof.)
lIsMovable :: Int -> Proof formula rule -> Bool
lIsMovable n p = fromMaybe False $ lIsMovable' n p
  where
    lIsMovable' :: Int -> Proof formula rule -> Maybe Bool
    lIsMovable' n _ | n < 0 = Just False
    lIsMovable' 0 (ProofLine _) = Just True
    lIsMovable' n (ProofLine _) = Nothing
    lIsMovable' n (SubProof fs ps l) | n < length fs = Just True
    lIsMovable' n (SubProof fs [] l) = Just False
    lIsMovable' n (SubProof fs (p : ps) l) = tryMovable (n - length fs) ps
      where
        tryMovable :: Int -> [Proof formula rule] -> Maybe Bool
        tryMovable n [] = Just False
        tryMovable n (p : ps) = lIsMovable' n p <|> tryMovable (n - lLength p) ps

-- `Maybe` is not needed here, maybe pull it inside a lRemove'
lRemove :: Int -> Proof formula rule -> Maybe (Proof formula rule)
lRemove _ (ProofLine _) = Nothing
lRemove n (SubProof fs ps l) | n < L.length fs = removeAt n fs >>= (\fs' -> pure $ SubProof fs' ps l)
lRemove n (SubProof fs ps l) = tryRemove (n - L.length fs) ps >>= (\ps' -> pure $ SubProof fs ps' l)
  where
    tryRemove :: Int -> [Proof formula rule] -> Maybe [Proof formula rule]
    tryRemove 0 ((ProofLine _) : ps) = Just ps
    tryRemove n (p@(ProofLine _) : ps) = tryRemove (n - 1) ps >>= \ps' -> return $ p : ps'
    tryRemove n (p@(SubProof {}) : ps) =
      maybe
        (tryRemove (n - lLength p) ps >>= \ps' -> return $ p : ps')
        (\p' -> Just $ p' : ps)
        (lRemove n p)
    tryRemove _ _ = Nothing

lInsert :: Either (Assumption formula) (Derivation formula rule) -> Int -> Proof formula rule -> Maybe (Proof formula rule)
lInsert (Left _) n (ProofLine _) = Nothing
lInsert (Left a) n (SubProof as ps d) = maybe (tryInsert a (n - length as) ps >>= (\ps' -> return $ SubProof as ps' d)) (\as' -> return $ SubProof as' ps d) (insertAt a n as)
  where
    tryInsert :: Assumption formula -> Int -> [Proof formula rule] -> Maybe [Proof formula rule]
    tryInsert a n (p : ps) = maybe (tryInsert a (n - lLength p) ps >>= (\ps' -> return $ p : ps')) (\p' -> return $ p' : ps) (lInsert (Left a) n p)
lInsert (Right (Derivation {})) n (ProofLine _) = Nothing
lInsert (Right d) 0 (SubProof fs ps l) = Just $ SubProof fs (ProofLine d : ps) l
lInsert (Right d) n (SubProof fs (p : ps) l) =
  maybe
    ( do
        p' <- lInsert (Right d) (n - lLength p) (SubProof fs ps l)
        case p' of
          ProofLine _ -> error ""
          SubProof fs' ps' l' -> return $ SubProof fs' (p : ps') l'
    )
    (\p' -> return $ SubProof fs (p' : ps) l)
    (lInsert (Right d) n p)