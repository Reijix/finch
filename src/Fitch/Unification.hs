module Fitch.Unification where

import Fitch.Proof

class FreeVars a where
  freeVars :: a -> [Name]
  makeFresh :: Name -> a -> Name
  makeFresh n t = if n `elem` freeVars t then makeFresh (n <> "'") t else n

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
(x : xs) ++! ys = x !: (xs ++! ys)

-- | Unique concatMap
concatMapU :: (Eq b) => (a -> [b]) -> [a] -> [b]
concatMapU f = foldr ((++!) . f) []

instance FreeVars Formula where
  freeVars :: Formula -> [Name]
  freeVars (Pred _ args) = concatMapU freeVars args
  freeVars (Opr _ fs) = concatMapU freeVars fs
  freeVars (Quantifier _ v f) = filter (/= v) $ freeVars f
  freeVars (FreshVar _) = []

instance FreeVars TermSpec where
  freeVars :: TermSpec -> [Name]
  freeVars (TVar n) = [n]
  freeVars (TFun _ ts) = concatMapU freeVars ts
  freeVars (TPlaceholder _) = []

instance FreeVars FormulaSpec where
  freeVars :: FormulaSpec -> [Name]
  freeVars (FPred _ args) = concatMapU freeVars args
  freeVars (FOpr _ fs) = concatMapU freeVars fs
  freeVars (FQuantifier _ v f) = filter (/= v) $ freeVars f
  freeVars (FSubst f (Subst v t)) = freeVars t
  freeVars (FFreshVar _) = []
  freeVars (FPlaceholder _) = []

fromTerm :: Term -> TermSpec
fromTerm (Var n) = TVar n
fromTerm (Fun f ts) = TFun f (map fromTerm ts)

class Substitute a b where
  subst :: Subst b -> a -> a

instance Substitute Term Term where
  subst :: Subst Term -> Term -> Term
  subst (Subst y s) t@(Var x) = if x == y then s else t
  subst sub (Fun f ts) = Fun f $ map (subst sub) ts

instance Substitute TermSpec TermSpec where
  subst :: Subst TermSpec -> TermSpec -> TermSpec
  subst (Subst y s) t@(TVar x) = if x == y then s else t
  subst sub (TFun f ts) = TFun f $ map (subst sub) ts

instance Substitute Formula Term where
  subst :: Subst Term -> Formula -> Formula
  subst sub (Pred name args) = Pred name (map (subst sub) args)
  subst sub (Opr op fs) = Opr op (map (subst sub) fs)
  subst s@(Subst x t) (Quantifier q v f)
    | x == v = Quantifier q v f
    | v `elem` freeVars t = subst (Subst x t) (Quantifier q v' f')
    | otherwise = Quantifier q v (subst s f)
   where
    v' = makeFresh (makeFresh v t) f
    f' = subst (Subst v (Var v')) f
  subst _ f = f

instance Substitute FormulaSpec TermSpec where
  subst :: Subst TermSpec -> FormulaSpec -> FormulaSpec
  subst sub (FPred name args) = FPred name (map (subst sub) args)
  subst sub (FOpr op fs) = FOpr op (map (subst sub) fs)
  subst s@(Subst x t) (FQuantifier q v f)
    | x == v = FQuantifier q v f
    | v `elem` freeVars t = subst (Subst x t) (FQuantifier q v' f')
    | otherwise = FQuantifier q v (subst s f)
   where
    v' = makeFresh (makeFresh v t) f
    f' = subst (Subst v (TVar v')) f
  subst s (FSubst n (Subst v' t')) =
    FSubst n (Subst v' (subst s t'))
  subst _ f = f

unifyTermSpec :: [(Term, TermSpec)] -> Maybe (Map Name Term)
unifyTermSpec ((Fun t ts, TFun s ss) : rest) | t == s && length ts == length ss = unifyTermSpec (zip ts ss ++ rest)
unifyTermSpec ((Var x, TVar y) : rest) | x == y = unifyTermSpec rest
unifyTermSpec ((t, TPlaceholder n) : rest) = (one (n, t) <>) <$> unifyTermSpec rest
unifyTermSpec [] = Just mempty
unifyTermSpec _ = Nothing

unifyTermsOnVariable :: Name -> [(Term, Term)] -> Maybe [(Name, Term)]
unifyTermsOnVariable n ts = do
  dc <- decompConflict ts
  case dc of
    (True, ts') -> unifyTermsOnVariable n ts'
    (False, ts') -> do
      edoo <- elimDeleteOccursOrient ts'
      case edoo of
        (True, ts'') -> unifyTermsOnVariable n ts''
        (False, ts'') -> makeUnificator ts''
 where
  decompConflict :: [(Term, Term)] -> Maybe (Bool, [(Term, Term)])
  decompConflict = undefined
  elimDeleteOccursOrient :: [(Term, Term)] -> Maybe (Bool, [(Term, Term)])
  elimDeleteOccursOrient = undefined
  makeUnificator :: [(Term, Term)] -> Maybe [(Name, Term)]
  makeUnificator = undefined

-- unifyTermsOnVariable :: Name -> [(Term, Term)] -> Maybe [(Name, Term)]
-- unifyTermsOnVariable n [] = Just []
-- unifyTermsOnVariable n ((Fun f ts, Fun g ss) : rest)
--   -- (decomp)
--   | f == g && length ts == length ss = unifyTermsOnVariable n (zip ts ss <> rest)
--   -- (conflict)
--   | otherwise = Nothing
-- -- (delete)
-- unifyTermsOnVariable n ((Var x, Var y) : rest) | x == y = unifyTermsOnVariable n rest
-- unifyTermsOnVariable n ((Var x, t) : rest)
--   -- (occurs)
--   | x `elem` freeVars t = Nothing
--   -- (elim)
--   | x `elem` concatMapU (\(t1, t2) -> freeVars t1 <> freeVars t2) rest =
--       unifyTermsOnVariable n $ (Var x, t) : map (bimap (subst (Subst x t)) (subst (Subst x t))) rest
--   | otherwise = ((x, t) :) <$> unifyTermsOnVariable n rest
-- -- (orient)
-- unifyTermsOnVariable n ((t@Fun{}, Var x) : rest) = unifyTermsOnVariable n ((Var x, t) : rest)
-- -- (orient (possibly) on variables)
-- unifyTermsOnVariable n ((t, Var x) : rest) | x == n = unifyTermsOnVariable n ((Var x, t) : rest)

unifyFormulaeOnVariable :: Name -> [(Formula, Formula)] -> Maybe (Map Name Term)
unifyFormulaeOnVariable n = fmap fromList . go
 where
  go :: [(Formula, Formula)] -> Maybe [(Name, Term)]
  go [] = Just []
  go ((Pred p ts, Pred q ss) : rest) | p == q && length ts == length ss = do
    mapping <- go rest
    unifyTermsOnVariable n $ zip ts ss <> map (first Var) mapping
  go ((Opr o1 fs1, Opr o2 fs2) : rest) | o1 == o2 && length fs1 == length fs2 = go (zip fs1 fs2 <> rest)
  go ((Quantifier q1 v1 f1, Quantifier q2 v2 f2) : rest) | q1 == q2 && v1 == v2 = go ((f1, f2) : rest)
  go _ = Nothing

unifyAlphaEq :: Formula -> FormulaSpec -> Maybe (Formula, FormulaSpec)
unifyAlphaEq f@(FreshVar v) fs@(FFreshVar v') = Just (f, fs)
unifyAlphaEq (FreshVar{}) _ = Nothing
unifyAlphaEq f@(Pred p ts) fs@(FPred p' ts')
  | p == p' && length ts == length ts' = do
      unifyTermSpec (zip ts ts')
      pure (f, fs)
unifyAlphaEq (Opr op fs) (FOpr op' fs')
  | op == op' = do
      fss <- zipWithM unifyAlphaEq fs fs'
      pure $ bimap (Opr op) (FOpr op') $ unzip fss
-- TODO the renaming for freshness needs to happen GLOBALLY!!
unifyAlphaEq f@(Quantifier q v form) fs@(FQuantifier q' v' form')
  | q == q' && v == v' = pure (f, fs)
  | q == q' && notElem v (freeVars form') = Just (f, FQuantifier q' v $ subst (Subst v (TVar v')) form')
  | q == q' =
      let
        v'' = makeFresh (makeFresh v form) form'
       in
        Just
          ( Quantifier q v'' $ subst (Subst v (Var v'')) form
          , FQuantifier q' v'' $ subst (Subst v (TVar v'')) form'
          )
unifyAlphaEq f fs@(FPlaceholder n) = Just (f, fs)
unifyAlphaEq f fs@(FSubst n sub) = pure (f, fs)
unifyAlphaEq _ _ = Nothing