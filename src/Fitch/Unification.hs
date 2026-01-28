module Fitch.Unification where

import Data.Set qualified as Set
import Fitch.Proof (
  Formula (FreshVar, Opr, Pred, Quantifier),
  FormulaSpec (
    FFreshVar,
    FOpr,
    FPlaceholder,
    FPred,
    FQuantifier,
    FSubst
  ),
  Name,
  Subst (..),
  Term (..),
  TermSpec (..),
  isFun,
 )
import Relude.Extra (delete, member, notMember)

-- * Collecting variables in structures

-- ** All variables

-- | Type class for structures that have variables occuring in them.
class AllVars a where
  -- | Returns all variables occuring in the structure
  allVars :: a -> Set Name

  {- | Takes a name and a structure and makes it fresh
  w.r.t. all the variables occuring in the structure.
  -}
  makeFresh :: Name -> a -> Name
  makeFresh n t = if n `member` allVars t then makeFresh (n <> "'") t else n

instance AllVars Term where
  allVars :: Term -> Set Name
  allVars (Var x) = one x
  allVars (Fun _ ts) = foldMap allVars ts

instance AllVars Formula where
  allVars :: Formula -> Set Name
  allVars (Pred _ args) = foldMap allVars args
  allVars (Opr _ fs) = foldMap allVars fs
  allVars (Quantifier _ v f) = one v <> allVars f
  allVars (FreshVar _) = mempty

-- ** Free variables

-- | Type class for structures that have variables occuring in them.
class FreeVars a where
  -- | Returns only the *free* (i.e. unbound) variables occuring in the structure.
  freeVars :: a -> Set Name

instance FreeVars Term where
  freeVars :: Term -> Set Name
  freeVars (Var x) = one x
  freeVars (Fun _ ts) = foldMap freeVars ts

instance FreeVars Formula where
  freeVars :: Formula -> Set Name
  freeVars (Pred _ args) = foldMap freeVars args
  freeVars (Opr _ fs) = foldMap freeVars fs
  freeVars (Quantifier _ v f) = Set.delete v $ freeVars f
  freeVars (FreshVar _) = mempty

-- * Substitution

-- | Type class for substitution.
class Substitute a b where
  {- | Takes a substitution and replaces variables occuring
  in the structure of type `a` with elements of type `b`.
  Of course this only makes sense if the type `a` also contains the type `b`.
  -}
  subst :: Subst b -> a -> a

instance Substitute Term Term where
  subst :: Subst Term -> Term -> Term
  subst (Subst y s) t@(Var x) = if x == y then s else t
  subst sub (Fun f ts) = Fun f $ map (subst sub) ts

instance Substitute Formula Term where
  subst :: Subst Term -> Formula -> Formula
  subst sub (Pred name args) = Pred name (map (subst sub) args)
  subst sub (Opr op fs) = Opr op (map (subst sub) fs)
  subst s@(Subst x t) (Quantifier q v f)
    | x == v = Quantifier q v f
    | v `member` freeVars t = subst (Subst x t) (Quantifier q v' f')
    | otherwise = Quantifier q v (subst s f)
   where
    v' = makeFresh (makeFresh v t) f
    f' = subst (Subst v (Var v')) f
  subst _ f = f

-- * Unification

{- | Unification on terms, this is the Martelli-Monatanari unification algorithm with a twist:
the unification happens "on" a variable @x@.
Meaning the resulting unificator must have the variable @x@ on the left hand side.
This is guaranteed by adding a new orient rule,
which orients assignments of the form @x := y@, where @y@ is also a variable.
-}
unifyTermsOnVariable :: Name -> [(Term, Term)] -> Maybe [(Name, Term)]
unifyTermsOnVariable n ts = do
  -- apply the rules until none of them match anymore.
  dc <- decompConflict ts
  case dc of
    (True, ts') -> unifyTermsOnVariable n ts'
    (False, ts') -> do
      edoo <- elimDeleteOccursOrient ts'
      case edoo of
        (True, ts'') -> unifyTermsOnVariable n ts''
        (False, ts'') -> makeUnificator ts''
 where
  {- Tries to apply the (decomp) or (conflict) rule,
  returns `Nothing` on failure (i.e. on conflict).
  Also returns whether the rule was applied, or no match was found. -}
  decompConflict :: [(Term, Term)] -> Maybe (Bool, [(Term, Term)])
  decompConflict ts = foldlM once (False, ts) ts
   where
    once :: (Bool, [(Term, Term)]) -> (Term, Term) -> Maybe (Bool, [(Term, Term)])
    once (_, list) tup@(Fun f args1, Fun g args2)
      -- (decomp)
      | f == g = Just (True, zip args1 args2 <> filter (/= tup) list)
      -- (conflict)
      | otherwise = Nothing
    once ret _ = Just ret

  {- Tries to apply the (elim), (occurs), (delete) and (orient) rules,
  returns `Nothing` on failure (i.e. on occurs).
  Also returns whether the rule was applied, or no match was found. -}
  elimDeleteOccursOrient :: [(Term, Term)] -> Maybe (Bool, [(Term, Term)])
  elimDeleteOccursOrient ts = foldlM once (False, ts) ts
   where
    once :: (Bool, [(Term, Term)]) -> (Term, Term) -> Maybe (Bool, [(Term, Term)])
    once (b, list) tup@(Var x, t)
      -- (occurs)
      | x `member` freeVars t = Nothing
      -- (elim)
      | x
          `member` foldMap
            (\(t1, t2) -> freeVars t1 <> freeVars t2)
            (filter (/= tup) list) =
          Just
            ( True
            , (Var x, t)
                : map
                  ( bimap
                      (subst (Subst x t))
                      (subst (Subst x t))
                  )
                  (filter (/= (Var x, t)) list)
            )
    -- (delete)
    once (_, list) tup@(Var x, Var y)
      | x == y =
          Just (True, filter (/= tup) list)
    -- (orient) [with special case to also orient `n`]
    once (_, list) tup@(t, Var x)
      | isFun t || x == n =
          Just (True, (Var x, t) : filter (/= tup) list)
    once ret _ = Just ret

  -- Turns a list of term tuples to a unificator.
  makeUnificator :: [(Term, Term)] -> Maybe [(Name, Term)]
  makeUnificator [] = Just []
  makeUnificator ((Var x, t) : rest) = ((x, t) :) <$> makeUnificator rest
  makeUnificator _ = Nothing

-- | Lifts `unifyTermsOnVariable` to formulae.
unifyFormulaeOnVariable :: Name -> [(Formula, Formula)] -> Maybe (Map Name Term)
unifyFormulaeOnVariable n = fmap fromList . go
 where
  go :: [(Formula, Formula)] -> Maybe [(Name, Term)]
  go [] = Just []
  go ((Pred p ts, Pred q ss) : rest) | p == q && length ts == length ss = do
    mapping <- go rest
    unifyTermsOnVariable n $ zip ts ss <> map (first Var) mapping
  go ((Opr o1 fs1, Opr o2 fs2) : rest)
    | o1 == o2 && length fs1 == length fs2 =
        go (zip fs1 fs2 <> rest)
  go ((Quantifier q1 v1 f1, Quantifier q2 v2 f2) : rest)
    | q1 == q2 && v1 == v2 =
        go ((f1, f2) : rest)
  go _ = Nothing

-- | Unify terms with a term specification.
termMatchesSpec :: [(Term, TermSpec)] -> Bool
termMatchesSpec ((Fun t ts, TFun s ss) : rest)
  | t == s && length ts == length ss =
      termMatchesSpec (zip ts ss ++ rest)
termMatchesSpec ((Var x, TVar y) : rest) = termMatchesSpec rest
termMatchesSpec ((t, TPlaceholder n) : rest) = termMatchesSpec rest
termMatchesSpec [] = True
termMatchesSpec _ = False

-- | Unify formula with formula specification.
formulaMatchesSpec :: Formula -> FormulaSpec -> Bool
formulaMatchesSpec f@(FreshVar v) fs@(FFreshVar v') = True
formulaMatchesSpec (FreshVar{}) _ = False
formulaMatchesSpec f@(Pred p ts) fs@(FPred p' ts')
  | p == p' && length ts == length ts' = termMatchesSpec (zip ts ts')
formulaMatchesSpec (Opr op fs) (FOpr op' fs')
  | op == op' = all (uncurry formulaMatchesSpec) (zip fs fs')
formulaMatchesSpec f@(Quantifier q v form) fs@(FQuantifier q' v' form')
  | q == q' = formulaMatchesSpec form form'
formulaMatchesSpec f fs@(FPlaceholder n) = True
formulaMatchesSpec f fs@(FSubst n sub) = True
formulaMatchesSpec _ _ = False