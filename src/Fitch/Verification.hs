module Fitch.Verification where

import App.Model (Model)
import Control.Monad (foldM, liftM2)
import Control.Monad.RWS (MonadState)
import Data.Bifunctor
import Data.Either (fromLeft)
import Data.Functor
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (fromJust)
import Data.Text (Text, append, pack)
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

unifyFormulae :: Formula -> FormulaSpec -> Maybe (Map Name Formula)
unifyFormulae (FreshVar v) (FFreshVar v') = Just $ M.singleton v' (FreshVar v)
unifyFormulae (FreshVar{}) _ = Nothing
unifyFormulae (Predicate p ts) (FPredicate p' ts')
  -- TODO do something here to handle `E = E`
  -- TODO check unifiability of terms!
  | p == p' && length ts == length ts' = Just M.empty
unifyFormulae (Op op fs) (FOp op' fs')
  | op == op' =
      foldM
        (\m (f, f') -> unifyFormulae f f' <&> M.union m)
        M.empty
        (zip fs fs')
unifyFormulae (Quantifier q v f) (FQuantifier q' v' f')
  -- TODO maybe rename this function so that it just adjusts alpha eq?
  | q == q' = undefined -- TODO alpha equivalence
unifyFormulae f (FVar n) = Just $ M.singleton n f
-- ignore the substitution, since it only replaces terms.
unifyFormulae f (FSubst fwp sub) = unifyFormulae f fwp
unifyFormulae _ _ = Nothing

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

canBeReferenced :: Int -> NodeAddr -> NodeAddr -> Maybe Text
canBeReferenced lineNo ruleLine refLine
  | ruleLine < refLine =
      Just $
        "Line "
          <> pack (show lineNo)
          <> " can not be referenced because it appears after this line.\n"
          <> pack (show ruleLine)
          <> " and "
          <> pack (show refLine)
  | ruleLine == refLine =
      Just "Can not reference the same line."
canBeReferenced lineNo (NAProof n (Just na1)) (NAProof m (Just na2))
  | n == m = canBeReferenced lineNo na1 na2
canBeReferenced lineNo _ (NAProof _ (Just _)) =
  Just $
    "Line "
      <> pack (show lineNo)
      <> " can not be referenced because it is located inside of a subproof."
canBeReferenced _ _ _ = Nothing

{- Phases of proof verification:
  1. Check that the rule exists
  2. Check that the formula matches the rules' conclusion.
  3. Check that the reference types (i.e. line or proof)
     match the expected assumptions and that references are visible for the current line.
  4. Check that the references match the expected assumptions,
     i.e. the form of the formula is correct.
  5. Collect name->term mappings.
  6. Verify name->term mappings, the datastructure should be `Map Name [Term]`
  7. Collect name->formula mappings, using the name->term mappings
     to resolve substitutions.
     The datastructure for name->formula mappings should be `
     Map Name [Either Formula [Formula]]`, where
     Name` is e.g. φ, `Formula` is a formula that has been identified as φ,
     and `[Formula]` is a list of possible formulae that
     can be identified as φ (yielded by backwards-substitution).
  8. Now check that for every φ all its mappings can be made equal by
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
        -- 3. Check that the reference types match expected assumptions.
        Right (conclusion, conclusionSpec) -> case verifyReferences 0 spec refs of
          Just err -> ParsedInvalid ruleText err ra
          -- 4. Check that formulae match given lines.
          Nothing -> case matchReferences spec refs of
            Left err -> ParsedInvalid ruleText err ra
            -- 5. Collect Name->Term mappings
            Right (formulaSpecs, proofSpecs) ->
              ParsedValid ruleText ra
   where
    formula = fromWrapper f
    formulaText = getText f
    ra@(RuleApplication ruleName refs) = fromWrapper r
    ruleText = getText r
    checkExistence :: Map Name RuleSpec -> Either Text RuleSpec
    checkExistence rules = case rules M.!? ruleName of
      Nothing -> Left ("Rule (" <> ruleName <> ") does not exist.")
      Just spec -> Right spec
    checkConclusion :: RuleSpec -> Formula -> Either Text (Formula, FormulaSpec)
    checkConclusion (RuleSpec _ _ expected) actual = case unifyFormulae actual expected of
      Nothing ->
        Left $
          "Rule cannot be applied to "
            <> formulaText
            <> "\nExpecting a formula of the form "
            <> pack (show expected)
      Just _ -> Right (actual, expected)
    matchReferences :: RuleSpec -> [Reference] -> Either Text ([(Formula, FormulaSpec)], [(Proof, ProofSpec)])
    -- formula
    matchReferences (RuleSpec (f : fs) ps c) (LineReference line : refs) =
      case unifyFormulae (extractFormula . fromJust $ pIndex line p) f of
        Nothing ->
          Left $
            "Found "
              <> (extractText . fromJust $ pIndex line p)
              <> " at line "
              <> pack (show line)
              <> ".\nBut expected a formula of the form "
              <> pack (show f)
              <> "."
        Just _ -> case matchReferences (RuleSpec fs ps c) refs of
          Left err -> Left err
          Right (fs, ps) -> Right ((extractFormula . fromJust $ pIndex line p, f) : fs, ps)
    -- proof
    matchReferences (RuleSpec [] (pSpec@(startFs, endF) : ps) c) (ProofReference start end : refs) =
      case pIndexProof start end p of
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
        Just p -> case handleProof (start, end) p pSpec of
          Just err -> Left err
          Nothing -> case matchReferences (RuleSpec [] ps c) refs of
            Left err -> Left err
            Right (fs, ps) -> Right (fs, (p, pSpec) : ps)
     where
      handleProof :: (Int, Int) -> Proof -> ProofSpec -> Maybe Text
      handleProof (_, end) (SubProof [] ps (Derivation c _)) ([], cSpec) = case unifyFormulae (fromWrapper c) cSpec of
        Nothing ->
          Just $
            "Found "
              <> getText c
              <> " at line "
              <> pack (show end)
              <> ".\nBut expected a formula of the form "
              <> pack (show cSpec)
              <> "."
        Just _ -> Nothing
      handleProof (start, end) (SubProof (f : fs) ps c) (fSpec : fSpecs, cSpec) = case unifyFormulae (fromWrapper f) fSpec of
        Nothing ->
          Just $
            "Found "
              <> getText f
              <> " at line "
              <> pack (show start)
              <> ".\nBut expected a formula of the form "
              <> pack (show cSpec)
              <> "."
        Just _ -> handleProof (start + 1, end) (SubProof fs ps c) (fSpecs, cSpec)
      -- TODO better error message
      handleProof _ (SubProof fs ps c) ([], cSpec) = Just "Rule expects a subproof with less assumptions!"
      handleProof _ (ProofLine{}) _ = error "handleProof got ProofLine (should not happen!)"
    matchReferences _ _ = Right ([], [])
    verifyReferences :: Int -> RuleSpec -> [Reference] -> Maybe Text
    verifyReferences n (RuleSpec (fSpec : fSpecs) ps f) (LineReference line : refs) =
      case pIndex line p of
        Just e ->
          case canBeReferenced line (fromJust $ fromLineNo ruleLine p) (fromJust $ fromLineNo line p) of
            Just err -> Just err
            Nothing -> case e of
              Left w ->
                if isParseValid w
                  then verifyReferences (n + 1) (RuleSpec fSpecs ps f) refs
                  else Just $ "Parse error in line: " <> pack (show line)
              Right (ProofLine (Derivation w _)) ->
                if isParseValid w
                  then verifyReferences (n + 1) (RuleSpec fSpecs ps f) refs
                  else Just $ "Parse error in line: " <> pack (show line)
        _ -> Just $ "Invalid line: " <> pack (show line)
    verifyReferences n (RuleSpec [] (pSpec : pSpecs) f) (ProofReference start end : refs) =
      case canBeReferenced start (fromJust $ fromLineNo ruleLine p) (fromJust $ fromLineNo start p) of
        Nothing -> verifyReferences (n + 1) (RuleSpec [] pSpecs f) refs
        Just err -> Just err
    verifyReferences n (RuleSpec (_ : _) _ _) (ProofReference start end : refs) =
      Just $
        "Rule ("
          <> ruleName
          <> ") expects a single line at position "
          <> pack (show n)
          <> " but got the range "
          <> pack (show start)
          <> "-"
          <> pack (show end)
          <> "."
    verifyReferences n (RuleSpec [] (_ : _) _) (LineReference line : refs) =
      Just $
        "Rule ("
          <> ruleName
          <> ") expects a line range at position "
          <> pack (show n)
          <> " but got the single line "
          <> pack (show line)
          <> "."
    verifyReferences n (RuleSpec (_ : fs) ps _) [] =
      Just $
        "Rule ("
          <> ruleName
          <> ") expects "
          <> pack (show $ n + length fs + length ps + 1)
          <> " references,\nbut got "
          <> pack (show n)
          <> " references."
    verifyReferences n (RuleSpec [] (_ : ps) _) [] =
      Just $
        "Rule ("
          <> ruleName
          <> ") expects "
          <> pack (show $ n + length ps + 1)
          <> " references,\nbut got "
          <> pack (show n)
          <> " references."
    verifyReferences n (RuleSpec [] [] _) (_ : refs) =
      Just $
        "Rule ("
          <> ruleName
          <> ") expects "
          <> pack (show n)
          <> " references,\nbut got "
          <> pack (show $ n + length refs + 1)
          <> " references."
    verifyReferences _ _ _ = Nothing