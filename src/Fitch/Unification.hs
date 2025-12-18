module Fitch.Unification where

import Data.Bifunctor
import Data.Text (append)
import Fitch.Proof

class FreeVars a where
  freeVars :: a -> [Name]

instance FreeVars Term where
  freeVars :: Term -> [Name]
  freeVars (Var x) = [x]
  freeVars (Fun _ ts) = foldr (\t ns -> foldr (!:) ns (freeVars t)) [] ts

-- | Unique insertion into lists
(!:) :: (Eq a) => a -> [a] -> [a]
x !: xs = if x `elem` xs then xs else x : xs

instance FreeVars FormulaWP where
  freeVars :: FormulaWP -> [Name]
  freeVars (FSubst f (Subst v t)) =
    foldr (!:) (filter (/= v) $ freeVars f) (freeVars t)
  freeVars (FVar{}) = []
  freeVars (FPredicate _ args) = concatMap freeVars args
  freeVars (FOp _ fs) = concatMap freeVars fs
  freeVars (FQuantifier _ v f) = filter (/= v) $ freeVars f

class MakeFresh a where
  makeFresh :: Name -> a -> Name

instance MakeFresh Term where
  makeFresh :: Name -> Term -> Name
  makeFresh n t = if n `elem` freeVars t then makeFresh (append n "'") t else n

instance MakeFresh FormulaWP where
  makeFresh :: Name -> FormulaWP -> Name
  makeFresh n (FSubst f (Subst _ t)) = makeFresh (makeFresh n f) t
  makeFresh n (FVar{}) = n
  makeFresh n (FPredicate name ts) = foldr (flip makeFresh) n ts
  makeFresh n (FOp _ fs) = foldr (flip makeFresh) n fs
  makeFresh n fq@(FQuantifier q v f) = if n `elem` (v : freeVars f) then makeFresh (append n "'") fq else n

class Substitute a where
  subst :: Subst -> a -> a

instance Substitute Term where
  subst :: Subst -> Term -> Term
  subst (Subst y s) t@(Var x) = if x == y then s else t
  subst sub (Fun f ts) = Fun f $ map (subst sub) ts

instance Substitute FormulaWP where
  subst :: Subst -> FormulaWP -> FormulaWP
  subst sub (FSubst f s) = error "unforeseen: calling subst on a `FSubst`" -- subst sub (subst s f)
  subst _ f@(FVar v) = f
  subst sub (FPredicate name args) = FPredicate name (map (subst sub) args)
  subst sub (FOp op fs) = FOp op (map (subst sub) fs)
  subst s@(Subst x t) (FQuantifier q v f)
    | x == v = FQuantifier q v f
    | v `elem` freeVars t = subst (Subst x t) (FQuantifier q v' f')
    | otherwise = FQuantifier q v (subst s f)
   where
    v' = makeFresh (makeFresh v t) f
    f' = subst (Subst v (Var v')) f

type Unifier a = [Subst]

class Unify a where
  unify :: [(a, a)] -> Maybe (Unifier a)

instance Unify Term where
  unify :: [(Term, Term)] -> Maybe (Unifier Term)
  unify [] = Just []
  -- (delete)
  unify ((Var x, Var y) : rest) | x == y = unify rest
  -- (decomp)
  unify ((Fun f es, Fun g ds) : rest) | f == g && length es == length ds = unify $ zip es ds ++ rest
  -- (conflict)
  unify ((Fun _ _, Fun _ _) : _) = Nothing
  -- (orient)
  unify ((Fun f ts, Var x) : rest) = unify $ (Var x, Fun f ts) : rest
  -- (occurs)
  unify ((Var x, t) : _) | x `elem` freeVars t && Var x /= t = Nothing
  -- (elim)
  unify ((Var x, t) : rest)
    | notElem x (freeVars t)
        && x `elem` concatMap (\(t1, t2) -> freeVars t1 ++ freeVars t2) rest =
        unify $ (Var x, t) : map (bimap (subst (x ~> t)) (subst (x ~> t))) rest
  -- descent
  unify ((Var x, s) : rest) = do
    rest' <- unify rest
    return $ (x ~> s) : rest'