module Fitch.Verification where

import App.Model (Model)
import Control.Monad (foldM, foldM_, forM, liftM2, zipWithM)
import Control.Monad.RWS (MonadState)
import Data.Bifunctor
import Data.Either (fromLeft)
import Data.Functor ((<&>))
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Text (Text, append, pack)
import Data.Traversable (mapAccumM)
import Fitch.Proof

class FreeVars a where
  freeVars :: a -> [Name]
  makeFresh :: Name -> a -> Name
  makeFresh n t = if n `elem` freeVars t then makeFresh (append n "'") t else n

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
  freeVars (FreshVar _) = []

instance FreeVars TermSpec where
  freeVars :: TermSpec -> [Name]
  freeVars (TVar n) = [n]
  freeVars (TFun _ ts) = concatMapU freeVars ts
  freeVars (TPlaceholder _) = []

instance FreeVars FormulaSpec where
  freeVars :: FormulaSpec -> [Name]
  freeVars (FPredicate _ args) = concatMapU freeVars args
  freeVars (FOp _ fs) = concatMapU freeVars fs
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
  subst sub (Predicate name args) = Predicate name (map (subst sub) args)
  subst sub (Op op fs) = Op op (map (subst sub) fs)
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
  subst sub (FPredicate name args) = FPredicate name (map (subst sub) args)
  subst sub (FOp op fs) = FOp op (map (subst sub) fs)
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
unifyTermSpec ((t, TPlaceholder n) : rest) = (M.singleton n t <>) <$> unifyTermSpec rest
unifyTermSpec [] = Just M.empty
unifyTermSpec _ = Nothing

unifyTerms :: [(Term, Term)] -> Maybe [(Name, Term)]
unifyTerms [] = Just []
unifyTerms ((Fun f ts, Fun g ss) : rest)
  -- (decomp)
  | f == g && length ts == length ss = unifyTerms (zip ts ss <> rest)
  -- (conflict)
  | otherwise = Nothing
-- (delete)
unifyTerms ((Var x, Var y) : rest) | x == y = unifyTerms rest
unifyTerms ((Var x, t) : rest)
  -- (occurs)
  | x `elem` freeVars t = Nothing
  -- (elim)
  | x `elem` concatMapU (\(t1, t2) -> freeVars t1 <> freeVars t2) rest =
      unifyTerms $ (Var x, t) : map (bimap (subst (Subst x t)) (subst (Subst x t))) rest
  | otherwise = ((x, t) :) <$> unifyTerms rest
-- (orient)
unifyTerms ((t, Var x) : rest) = unifyTerms ((Var x, t) : rest)

unifyFormulae :: [(Formula, Formula)] -> Maybe (Map Name Term)
unifyFormulae = fmap M.fromList . go
 where
  go :: [(Formula, Formula)] -> Maybe [(Name, Term)]
  go ((Predicate p ts, Predicate q ss) : rest) | p == q && length ts == length ss = do
    mapping <- go rest
    unifyTerms $ zip ts ss <> map (first Var) mapping
  go ((Op o1 fs1, Op o2 fs2) : rest) | o1 == o2 && length fs1 == length fs2 = go (zip fs1 fs2 <> rest)
  go ((Quantifier q1 v1 f1, Quantifier q2 v2 f2) : rest) | q1 == q2 && v1 == v2 = go ((f1, f2) : rest)
  go _ = Nothing

unifyAlphaEq :: Formula -> FormulaSpec -> Maybe (Formula, FormulaSpec)
unifyAlphaEq f@(FreshVar v) fs@(FFreshVar v') = Just (f, fs)
unifyAlphaEq (FreshVar{}) _ = Nothing
unifyAlphaEq f@(Predicate p ts) fs@(FPredicate p' ts')
  | p == p' && length ts == length ts' = do
      unifyTermSpec (zip ts ts')
      return (f, fs)
unifyAlphaEq (Op op fs) (FOp op' fs')
  | op == op' = do
      fss <- zipWithM unifyAlphaEq fs fs'
      return $ bimap (Op op) (FOp op') $ unzip fss
-- TODO the renaming for freshness needs to happen GLOBALLY!!
unifyAlphaEq f@(Quantifier q v form) fs@(FQuantifier q' v' form')
  | q == q' && v == v' = return (f, fs)
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
unifyAlphaEq f fs@(FSubst n sub) = return (f, fs)
unifyAlphaEq _ _ = Nothing

{- Phases of proof verification:
  1. Check that the rule exists
  2. Check that the formula matches the rules' conclusion.
  3. Match references to lines/proof, concretely:
    - check that references are parsed and valid line numbers
    - line references should only refer to lines
    - proof references should refer to proofs,
      i.e. first number is the first line and second number the conclusion
    - referenced line needs to be visible for the referer,
      i.e. not in a subproof or later in the proof.
    - unify referenced lines with expected formula/proof.
  4. Collect name->term mappings.
  5. Verify name->term mappings, the datastructure should be `Map Name [(Int, Term)]`
     to give better error messages. The `Int` is the corresponding line number.
  6. Collect name->formula mappings, using the name->term mappings
     to resolve substitutions.
     The datastructure for name->formula mappings should be
     `Map Name [Either Formula [Formula]]`, where
     `Name` is e.g. φ, `Formula` is a formula that has been identified as φ,
     and `[Formula]` is a list of possible formulae that
     can be identified as φ (yielded by backwards-substitution).
  7. Now check that for every φ all its mappings can be made equal by
     choosing from the lists.
 -}
verifyProof :: Map Name RuleSpec -> Proof -> Proof
verifyProof rules p = pMapWithLineNo (const id) verifyRule p
 where
  verifyRule :: Int -> Derivation -> Derivation
  verifyRule _ d@(Derivation _ (Unparsed{})) = d
  verifyRule _ d@(Derivation f@(Unparsed{}) r) = Derivation f $ ParsedInvalid (getText r) "Parse error in formula." (fromWrapper r)
  verifyRule ruleLine (Derivation f r) =
    -- 1. Check that the rule exists.
    Derivation f $ case checkExistence rules of
      Left err -> ParsedInvalid ruleText err ra
      -- 2. Check that the formula matches the rules' conclusion.
      Right spec -> case checkConclusion spec formula of
        Left err -> ParsedInvalid ruleText err ra
        -- 3. Match each reference to the corresponding line/proof
        Right (conclusion, conclusionSpec) -> case unifyReferences 0 spec refs of
          Left err -> ParsedInvalid ruleText err ra
          -- 4. Collect name->term mappings and 5. verify term mappings
          Right formulaSpecs -> case verifyTerms (collectTerms ((conclusion, conclusionSpec) : formulaSpecs)) of
            Left err -> ParsedInvalid ruleText err ra
            Right termMap -> case verifyFormulae termMap ((conclusion, conclusionSpec) : formulaSpecs) of
              Left err -> ParsedInvalid ruleText err ra
              Right formMap -> ParsedInvalid ruleText (pack $ show formMap) ra
   where
    ---------------------------------------------------
    -- Unwrap variables
    formula = fromWrapper f
    formulaText = getText f
    ra@(RuleApplication ruleName refs) = fromWrapper r
    ruleText = getText r
    ---------------------------------------------------

    ---------------------------------------------------
    -- 1. Check that the rule exists.
    checkExistence :: Map Name RuleSpec -> Either Text RuleSpec
    checkExistence rules = case rules M.!? ruleName of
      Nothing -> Left ("Rule (" <> ruleName <> ") does not exist.")
      Just spec -> Right spec
    ---------------------------------------------------

    ---------------------------------------------------
    -- 2. Unify conclusion.
    checkConclusion :: RuleSpec -> Formula -> Either Text (Formula, FormulaSpec)
    checkConclusion (RuleSpec _ _ expected) actual = case unifyAlphaEq actual expected of
      Nothing ->
        Left $
          "Rule cannot be applied to "
            <> formulaText
            <> "\nExpecting a formula of the form "
            <> pack (show expected)
      Just (actual', expected') -> Right (actual', expected')
    ---------------------------------------------------

    ---------------------------------------------------
    -- 3. Unify references
    handleFormula :: Int -> Formula -> FormulaSpec -> Either Text (Formula, FormulaSpec)
    handleFormula line f fSpec = case unifyAlphaEq f fSpec of
      Nothing ->
        Left $
          "Found "
            <> pack (show f)
            <> " at line "
            <> pack (show line)
            <> ".\nBut expected a formula of the form "
            <> pack (show fSpec)
            <> "."
      Just (f', fSpec') -> Right (f', fSpec')
    handleAssumption :: Int -> Assumption -> FormulaSpec -> Either Text (Formula, FormulaSpec)
    handleAssumption line fw fSpec = case fw of
      Unparsed{} -> Left "Unparsed assumption --- INTERNAL ERROR SHOULD NOT HAPPEN"
      (ParsedInvalid txt err f) -> do
        (f', fSpec') <- handleFormula line f fSpec
        return (f', fSpec')
      (ParsedValid txt f) -> do
        (f', fSpec') <- handleFormula line f fSpec
        return (f', fSpec')
    unifyReferences :: Int -> RuleSpec -> [Reference] -> Either Text [(Formula, FormulaSpec)]
    unifyReferences n (RuleSpec (fSpec : fSpecs) pSpecs cSpec) (LineReference refLine : refs) = do
      f <- lookupReference refLine p
      f' <- handleFormula refLine f fSpec
      fs <- unifyReferences (n + 1) (RuleSpec fSpecs pSpecs cSpec) refs
      return (f' : fs)
    unifyReferences n (RuleSpec [] (pSpec : pSpecs) cSpec) (ProofReference start end : refs) = case pIndexProof start end p of
      Nothing ->
        Left $
          "Line range "
            <> pack (show start)
            <> "-"
            <> pack (show end)
            <> " does not correspond to a subproof.\nLine "
            <> pack (show start)
            <> " should mark the start of a subproof and line "
            <> pack (show end)
            <> " should be its conclusion."
      Just prf -> do
        case (fromLineNo ruleLine p, fromLineRange start end p) of
          (Nothing, _) -> Left $ "Line " <> pack (show ruleLine) <> " is not a valid line. INTERNAL ERROR, SHOULD NOT HAPPEN"
          (_, Nothing) -> Left $ "Line range " <> pack (show start) <> "-" <> pack (show end) <> " is not a valid range. INTERNAL ERROR, SHOULD NOT HAPPEN"
          (Just ruleAddr, Just refAddr) -> case refIsVisible start ruleAddr refAddr of
            Nothing -> Right ()
            Just err -> Left err
        fs <- handleProof (start, end) prf pSpec
        fs' <- unifyReferences (n + 1) (RuleSpec [] pSpecs cSpec) refs
        return (fs ++ fs')
     where
      handleProof :: (Int, Int) -> Proof -> ProofSpec -> Either Text [(Formula, FormulaSpec)]
      handleProof (start, end) (SubProof fs ps (Derivation c r)) (fSpecs, cSpec)
        | length fs /= length fSpecs = Left "Number of assumptions of the subproof does not match the expected number."
        | otherwise = do
            (fs', fSpecs') <-
              unzip . snd
                <$> mapAccumM
                  ( \s (a, fSpec) -> do
                      (a', fSpec') <- handleAssumption s a fSpec
                      return (s + 1, (a', fSpec'))
                  )
                  start
                  (zip fs fSpecs)
            (c', cSpec') <- handleAssumption end c cSpec
            return (zip (fs' ++ [c']) (fSpecs' ++ [cSpec']))
      handleProof _ (ProofLine{}) _ = Left "handleProof found ProofLine -- SHOULD NOT HAPPEN - INTERNAL ERROR."
    unifyReferences n (RuleSpec (_ : _) _ _) (ProofReference start end : refs) =
      Left $
        "Rule ("
          <> ruleName
          <> ") expects a single line at position "
          <> pack (show n)
          <> " but got the range "
          <> pack (show start)
          <> "-"
          <> pack (show end)
          <> "."
    unifyReferences n (RuleSpec _ (_ : _) _) (LineReference line : refs) =
      Left $
        "Rule ("
          <> ruleName
          <> ") expects a line range at position "
          <> pack (show n)
          <> " but got the single line "
          <> pack (show line)
          <> "."
    unifyReferences n (RuleSpec (_ : fs) ps _) [] =
      Left $
        "Rule ("
          <> ruleName
          <> ") expects "
          <> pack (show $ n + length fs + length ps + 1)
          <> " references,\nbut got "
          <> pack (show n)
          <> " references."
    unifyReferences n (RuleSpec [] (_ : ps) _) [] =
      Left $
        "Rule ("
          <> ruleName
          <> ") expects "
          <> pack (show $ n + length ps + 1)
          <> " references,\nbut got "
          <> pack (show n)
          <> " references."
    unifyReferences n (RuleSpec [] [] _) (_ : refs) =
      Left $
        "Rule ("
          <> ruleName
          <> ") expects "
          <> pack (show n)
          <> " references,\nbut got "
          <> pack (show $ n + length refs + 1)
          <> " references."
    unifyReferences _ (RuleSpec [] [] _) [] = Right []
    ---------------------------------------------------

    ---------------------------------------------------
    -- 4. Collect terms
    collectTerms :: [(Formula, FormulaSpec)] -> Map Name [Term]
    collectTerms ((Predicate _ ps, FPredicate _ qs) : rest) =
      M.unionWith
        (++)
        (collectTerms' (zip ps qs))
        (collectTerms rest)
     where
      collectTerms' :: [(Term, TermSpec)] -> Map Name [Term]
      collectTerms' [] = M.empty
      collectTerms' ((Fun _ ts, TFun _ ss) : rest) = collectTerms' (zip ts ss ++ rest)
      collectTerms' ((t, TPlaceholder n) : rest) =
        M.insertWith
          (++)
          n
          [t]
          (collectTerms' rest)
      collectTerms' (_ : rest) = collectTerms' rest
    collectTerms ((Op _ fs, FOp _ fs') : rest) =
      collectTerms (zip fs fs' ++ rest)
    collectTerms ((Quantifier _ _ f, FQuantifier _ _ f') : rest) =
      collectTerms ((f, f') : rest)
    collectTerms ((FreshVar m, FFreshVar n) : rest) = M.insertWith (++) n [Var m] $ collectTerms rest
    collectTerms (_ : rest) = collectTerms rest
    collectTerms [] = M.empty
    ---------------------------------------------------

    ---------------------------------------------------
    -- 5. Verify term mappings
    verifyTerms :: Map Name [Term] -> Either Text (Map Name Term)
    verifyTerms m = M.fromList <$> mapM makeUnique (M.toList m)
     where
      makeUnique :: (Name, [Term]) -> Either Text (Name, Term)
      makeUnique (_, []) = Left "INTERNAL ERROR, makeUnique got empty list of Terms!"
      makeUnique (v, t : ts) = do
        foldM_
          ( \lastTerm currTerm ->
              if lastTerm == currTerm
                then Right currTerm
                else
                  Left $
                    "Error when trying to verify that\nall assignments of placeholder "
                      <> v
                      <> " are the same, found\n"
                      <> v
                      <> "↦"
                      <> pack (show lastTerm)
                      <> " and\n"
                      <> v
                      <> "↦"
                      <> pack (show currTerm)
                      <> "."
          )
          t
          ts
        return (v, t)
    ---------------------------------------------------

    ---------------------------------------------------
    -- 6. Collect formula mappings using backward substitution
    verifyFormulae :: Map Name Term -> [(Formula, FormulaSpec)] -> Either Text (Map Name Formula)
    verifyFormulae termMap formsAndSpecs = do
      formMap <- reduceFormulae $ M.map (NE.map Left) $ collectSimpleFormulae formsAndSpecs
      formMap' <- collectMoreFormulae formMap formsAndSpecs
      reduceFormulae formMap'
     where
      collectSimpleFormulae :: [(Formula, FormulaSpec)] -> Map Name (NonEmpty Formula)
      collectSimpleFormulae [] = M.empty
      collectSimpleFormulae ((Predicate{}, FPredicate{}) : rest) = collectSimpleFormulae rest
      collectSimpleFormulae ((Op _ fs, FOp _ fSpecs) : rest) = collectSimpleFormulae $ zip fs fSpecs <> rest
      collectSimpleFormulae ((Quantifier _ _ f, FQuantifier _ _ fSpec) : rest) = collectSimpleFormulae $ (f, fSpec) : rest
      collectSimpleFormulae ((FreshVar n, FFreshVar m) : rest) = collectSimpleFormulae rest
      collectSimpleFormulae ((f, FPlaceholder n) : rest) = M.insertWith (<>) n (f :| []) $ collectSimpleFormulae rest
      collectSimpleFormulae (_ : rest) = collectSimpleFormulae rest
      reduceFormulae :: Map Name (NonEmpty (Either Formula [Formula])) -> Either Text (Map Name Formula)
      reduceFormulae = M.traverseWithKey reduceHelper
       where
        reduceHelper :: Name -> NonEmpty (Either Formula [Formula]) -> Either Text Formula
        reduceHelper n (Left f :| rest) = go n f rest
        reduceHelper n (Right [] :| rest) = Left "Error: can't find match!"
        reduceHelper n (Right (f : fs) :| rest) = case go n f rest of
          Left err -> reduceHelper n (Right fs :| rest)
          Right f -> Right f
        go :: Name -> Formula -> [Either Formula [Formula]] -> Either Text Formula
        go n f [] = Right f
        go n f (Left f' : rest) = if f == f' then go n f' rest else Left "Error f/=f'" -- TODO error message
        go n f (Right fs' : rest) = mapFs fs'
         where
          mapFs :: [Formula] -> Either Text Formula
          mapFs [] = Left $ "Error: can't find match for f=" <> pack (show f)
          mapFs (f' : fs) = if f /= f' then mapFs fs else Right f'

      collectMoreFormulae :: Map Name Formula -> [(Formula, FormulaSpec)] -> Either Text (Map Name (NonEmpty (Either Formula [Formula])))
      collectMoreFormulae formMap [] = Right . M.map (\f -> Left f :| []) $ formMap
      collectMoreFormulae formMap ((f, FSubst phi (Subst n t)) : rest) = case formMap M.!? phi of
        -- unify fs
        Just phiF -> case unifyFormulae [(phiF, f)] of
          Nothing -> Left $ "Error unifying " <> pack (show phiF) <> " with\n" <> pack (show f)
          -- compare assignment of E
          Just mgu -> case (mgu M.!? n, termMap M.!? n) of
            (Nothing, _) -> M.insertWith (<>) phi (Left phiF :| []) <$> collectMoreFormulae formMap rest
            (Just e, Just e') -> undefined
        Nothing -> case t of
          TPlaceholder e -> case termMap M.!? e of
            Nothing -> Left "Term has wrong form, RULEERROR!" -- error
            Just t -> undefined -- backward substitution
          _ -> Left "Term has wrong form, RULEERROR!" -- error
      collectMoreFormulae formMap (_ : rest) = collectMoreFormulae formMap rest
      substBackwardsForm :: Subst Term -> Formula -> [Formula]
      substBackwardsForm s (Predicate p ts) = map (Predicate p) . transpose $ map (substBackwardsTerm s) ts
      substBackwardsForm s (Op o fs) = map (Op o) . transpose $ map (substBackwardsForm s) fs
      -- TODO need freshness here :(
      substBackwardsForm s@(Subst n t) (Quantifier q v f) = if n == v then undefined else map (Quantifier q v) (substBackwardsForm s f)
      substBackwardsForm _ f = error "tried substBackwardsForm on FreshVar"
      substBackwardsTerm :: Subst Term -> Term -> [Term]
      substBackwardsTerm s@(Subst n e) t | t == e = [Var n, t]
      substBackwardsTerm s (Var x) = [Var x]
      substBackwardsTerm s (Fun f ts) = map (Fun f) . transpose $ map (substBackwardsTerm s) ts
      transpose :: [[a]] -> [[a]]
      transpose [] = []
      transpose (l : rest) = let rest' = transpose rest in concatMap (\t -> map (t :) rest') l
    ---------------------------------------------------

    -- helpers
    refIsVisible :: Int -> NodeAddr -> NodeAddr -> Maybe Text
    refIsVisible line ruleAddr refAddr
      | ruleAddr <= refAddr = Just "Can only reference lines that appear before this line!"
    refIsVisible line (NAProof n (Just na1)) (NAProof m (Just na2))
      | n == m = refIsVisible line na1 na2
    refIsVisible line rua ra@(NAProof _ (Just _)) = Just "Line cannot be referenced because it is located inside of a subproof."
    refIsVisible _ _ _ = Nothing

    lookupReference :: Int -> Proof -> Either Text Formula
    lookupReference refLine p
      | ruleLine < refLine =
          Left $
            "Line "
              <> pack (show refLine)
              <> " can not be referenced because it appears after this line."
      | ruleLine == refLine =
          Left "Can not reference the same line."
    lookupReference refLine p = case (fromLineNo ruleLine p, fromLineNo refLine p) of
      (Nothing, _) -> Left $ "Line " <> pack (show ruleLine) <> " is not a valid line. INTERNAL ERROR, SHOULD NOT HAPPEN"
      (_, Nothing) -> Left $ "Line " <> pack (show refLine) <> " is not a valid line. INTERNAL ERROR, SHOULD NOT HAPPEN"
      (Just ruleAddr, Just refAddr) ->
        maybe
          ( case pIndex refLine p of
              Nothing -> Left $ "Line " <> pack (show refLine) <> " is not a valid line."
              Just (Left (ParsedValid _ f)) -> Right f
              Just (Right (Derivation (ParsedValid _ f) _)) -> Right f
              Just _ -> Left $ "Parse error in line: " <> pack (show refLine)
          )
          Left
          (refIsVisible refLine ruleAddr refAddr)