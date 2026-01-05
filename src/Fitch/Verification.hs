module Fitch.Verification where

import App.Model (Model)
import Control.Monad (foldM, liftM2)
import Control.Monad.RWS (MonadState)
import Data.Bifunctor
import Data.Functor
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text (Text, append)
import Fitch.Proof

class FreeVars a where
  freeVars :: a -> [Name]

instance FreeVars Term where
  freeVars :: Term -> [Name]
  freeVars (Var x) = [x]
  freeVars (Fun _ ts) = concatMapU freeVars ts

-- | Unique insertion into lists
(!:) :: (Eq a) => a -> [a] -> [a]
x !: xs = if x `elem` xs then xs else x : xs

-- | Unique appending
(++!) :: (Eq a) => [a] -> [a] -> [a]
[] ++! ys = ys
(x : xs) ++! ys = x !: xs ++! ys

-- | Unique concatMap
concatMapU :: (Eq b) => (a -> [b]) -> [a] -> [b]
concatMapU f = foldr ((++!) . f) []

instance FreeVars Formula where
  freeVars :: Formula -> [Name]
  freeVars (Predicate _ args) = concatMapU freeVars args
  freeVars (Op _ fs) = concatMapU freeVars fs
  freeVars (Quantifier _ v f) = filter (/= v) $ freeVars f

class MakeFresh a where
  makeFresh :: Name -> a -> Name

instance MakeFresh Term where
  makeFresh :: Name -> Term -> Name
  makeFresh n t = if n `elem` freeVars t then makeFresh (append n "'") t else n

instance MakeFresh Formula where
  makeFresh :: Name -> Formula -> Name
  makeFresh n (Predicate name ts) = foldr (flip makeFresh) n ts
  makeFresh n (Op _ fs) = foldr (flip makeFresh) n fs
  makeFresh n fq@(Quantifier q v f) = if n `elem` (v : freeVars f) then makeFresh (append n "'") fq else n

class Substitute a where
  subst :: Subst -> a -> a

instance Substitute Term where
  subst :: Subst -> Term -> Term
  subst (Subst y s) t@(Var x) = if x == y then s else t
  subst sub (Fun f ts) = Fun f $ map (subst sub) ts

instance Substitute Formula where
  subst :: Subst -> Formula -> Formula
  subst sub (Predicate name args) = Predicate name (map (subst sub) args)
  subst sub (Op op fs) = Op op (map (subst sub) fs)
  subst s@(Subst x t) (Quantifier q v f)
    | x == v = Quantifier q v f
    | v `elem` freeVars t = subst (Subst x t) (Quantifier q v' f')
    | otherwise = Quantifier q v (subst s f)
   where
    v' = makeFresh (makeFresh v t) f
    f' = subst (Subst v (Var v')) f

-- | Returns `True` if all formulae of the proof have been successfully parsed and are semantically valid.
formulaeValid :: Proof -> Bool
formulaeValid =
  pFold
    (\b a -> b && isParseValid a)
    (\b (Derivation f _) -> b && isParseValid f)
    True

unifyFormulae :: Formula -> FormulaWP -> Maybe (Map Name Formula)
unifyFormulae (Predicate p ts) (FPredicate p' ts')
  -- TODO do something here to handle `E = E`
  | p == p' && length ts == length ts' = Just M.empty
unifyFormulae (Op op fs) (FOp op' fs')
  | op == op' =
      foldM
        (\m (f, f') -> unifyFormulae f f' <&> M.union m)
        M.empty
        (zip fs fs')
unifyFormulae (Quantifier q v f) (FQuantifier q' v' f')
  | q == q' = undefined -- TODO alpha equivalence
unifyFormulae f (FVar n) = Just $ M.singleton n f
-- ignore the substitution, since it only replaces terms.
unifyFormulae f (FSubst fwp sub) = unifyFormulae f fwp
unifyFormulae _ _ = Nothing

{- Phases of proof verification:
  1. Check that the formula matches the rules' conclusion.
  2. Check that the reference types (i.e. line or proof) match the expected assumptions.
  3. Check that the references match the expected assumptions, i.e. the form of the formula is correct.
  4. Collect name->term mappings.
  5. Verify name->term mappings, the datastructure should be `Map Name [Term]`
  5. Collect name->formula mappings, using the name->term mappings to resolve substitutions.
     The datastructure for name->formula mappings should be `Map Name [Either Formula [Formula]]`, where
     Name` is e.g. φ, `Formula` is a formula that has been identified as φ,
     and `[Formula]` is a list of possible formulae that
     can be identified as φ (yielded by backwards-substitution).
  6. Now check that for every φ all its mappings can be made equal by choosing from the lists.
 -}
verifyProof :: Map Name RuleSpec -> Proof -> Proof
verifyProof rules = pMap id verifyRule
 where
  verifyRule :: Derivation -> Derivation
  verifyRule d@(Derivation _ (Unparsed{})) = d
  verifyRule (Derivation f r) =
    let
      formula = fromWrapper f
      ra@(RuleApplication ruleName refs) = fromWrapper r
      text = getText r
     in
      Derivation f $ case rules M.!? ruleName of
        Nothing -> ParsedInvalid text ("Rule (" `append` ruleName `append` ") does not exist.") ra
        Just spec -> case verifyReferences spec refs formula of
          Nothing -> ParsedValid text ra
          Just err -> ParsedInvalid text err ra
  verifyReferences :: RuleSpec -> [Reference] -> Formula -> Maybe Text
  verifyReferences _ _ _ = Nothing