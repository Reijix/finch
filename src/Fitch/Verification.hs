module Fitch.Verification where

import App.Model (Model)
import Control.Monad (foldM, forM, liftM2, zipWithM)
import Control.Monad.RWS (MonadState)
import Data.Bifunctor
import Data.Either (fromLeft)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Text (Text, append, pack)
import Data.Traversable (mapAccumM)
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

-- TODO makeFresh is erronous when chained...
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

unifyAlphaEq :: Formula -> FormulaSpec -> Maybe (Formula, FormulaSpec)
unifyAlphaEq f@(FreshVar v) fs@(FFreshVar v') = Just (f, fs)
unifyAlphaEq (FreshVar{}) _ = Nothing
unifyAlphaEq f@(Predicate p ts) fs@(FPredicate p' ts')
  | p == p' && length ts == length ts' = do
      unifyTermsOnlyFun (zip ts ts')
      return (f, fs)
 where
  unifyTermsOnlyFun :: [(Term, Term)] -> Maybe ()
  unifyTermsOnlyFun ((Fun t ts, Fun s ss) : rest) | t == s && length ts == length ss = unifyTermsOnlyFun (zip ts ss ++ rest)
  unifyTermsOnlyFun ((Var _, Var _) : rest) = unifyTermsOnlyFun rest
  unifyTermsOnlyFun _ = Nothing
unifyAlphaEq (Op op fs) (FOp op' fs')
  | op == op' = do
      fss <- zipWithM unifyAlphaEq fs fs'
      return $ bimap (Op op) (FOp op') $ unzip fss
unifyAlphaEq f@(Quantifier q v form) fs@(FQuantifier q' v' form')
  | q == q' = return (f, fs)
  | otherwise = undefined
unifyAlphaEq f fs@(FVar n) = Just (f, fs)
-- ignore the substitution, since it only replaces terms.
unifyAlphaEq f fs@(FSubst fwp sub) = do
  (f', fwp') <- unifyAlphaEq f fwp
  return (f', FSubst fwp' sub)
unifyAlphaEq _ _ = Nothing

unifyTermsDirected :: [(Term, Term)] -> Map Name [Term]
unifyTermsDirected [] = M.empty
unifyTermsDirected ((Var x, t) : rest) =
  M.alter (\case Nothing -> Just [t]; Just ts -> Just $ t : ts) x $ unifyTermsDirected rest
unifyTermsDirected ((Fun f es, Fun g ds) : rest) = unifyTermsDirected (zip es ds)

unifyFormulaeTerm :: Formula -> FormulaSpec -> Map Name [Term]
unifyFormulaeTerm (Predicate _ ts) (FPredicate _ ts') =
  unifyTermsDirected (zip ts' ts)
unifyFormulaeTerm (Op _ fs) (FOp _ fs') = foldr (M.union . uncurry unifyFormulaeTerm) M.empty (zip fs fs')
unifyFormulaeTerm (Quantifier _ _ f) (FQuantifier _ _ f') = unifyFormulaeTerm f f'
unifyFormulaeTerm _ _ = M.empty

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
     The datastructure for name->formula mappings should be `
     Map Name [Either Formula [Formula]]`, where
     Name` is e.g. φ, `Formula` is a formula that has been identified as φ,
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
          -- 4. Collect name->term mappings
          Right (formulaSpecs, proofSpecs) -> ParsedValid ruleText ra
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
    handleAssumption :: Int -> Assumption -> FormulaSpec -> Either Text (Assumption, FormulaSpec)
    handleAssumption line fw fSpec = case fw of
      Unparsed{} -> Left "Unparsed assumption --- INTERNAL ERROR SHOULD NOT HAPPEN"
      (ParsedInvalid txt err f) -> do
        (f', fSpec') <- handleFormula line f fSpec
        return (ParsedInvalid txt err f', fSpec')
      (ParsedValid txt f) -> do
        (f', fSpec') <- handleFormula line f fSpec
        return (ParsedValid txt f', fSpec')
    unifyReferences :: Int -> RuleSpec -> [Reference] -> Either Text ([(Formula, FormulaSpec)], [(Proof, ProofSpec)])
    unifyReferences n (RuleSpec (fSpec : fSpecs) pSpecs cSpec) (LineReference refLine : refs) = do
      f <- lookupReference refLine p
      f' <- handleFormula refLine f fSpec
      (fs, ps) <- unifyReferences (n + 1) (RuleSpec fSpecs pSpecs cSpec) refs
      return (f' : fs, ps)
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
        (p', pSpec') <- handleProof (start, end) prf pSpec
        (fs, ps) <- unifyReferences (n + 1) (RuleSpec [] pSpecs cSpec) refs
        return (fs, (p', pSpec') : ps)
     where
      handleProof :: (Int, Int) -> Proof -> ProofSpec -> Either Text (Proof, ProofSpec)
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
            return (SubProof fs' ps (Derivation c' r), (fSpecs', cSpec'))
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
    unifyReferences _ (RuleSpec [] [] _) [] = Right ([], [])
    ---------------------------------------------------

    ---------------------------------------------------
    -- 4. Collect terms
    collectTerms :: [(Formula, FormulaSpec)] -> [(Proof, ProofSpec)] -> Map Name [(Int, Term)]
    collectTerms fs ps = undefined
    ---------------------------------------------------

    ---------------------------------------------------
    -- 5. Verify term mappings
    verifyTerms :: Map Name [(Int, Term)] -> Either Text (Map Name Term)
    verifyTerms = undefined
    ---------------------------------------------------

    -- helpers
    refIsVisible :: Int -> NodeAddr -> NodeAddr -> Maybe Text
    refIsVisible line ruleAddr refAddr
      | ruleAddr <= refAddr = Just "Can only reference lines that appear before this line!"
    refIsVisible line (NAProof n (Just na1)) (NAProof m (Just na2))
      | n == m = refIsVisible line na1 na2
    refIsVisible _ (NAProof n _) (NAProof m _) | m < n = Nothing
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