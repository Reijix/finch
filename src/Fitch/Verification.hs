module Fitch.Verification where

import App.Model (Model)
import Data.Map qualified as M
import Data.Traversable (mapAccumM)
import Fitch.Proof
import Fitch.Unification
import Relude.Extra.Map

{-@ allCombinations :: xss:[[a]] -> [{v:[a]| len v == len xss}] @-}
allCombinations :: [[a]] -> [[a]]
allCombinations xs = assert (all ((length xs ==) . length)) $ go xs
 where
  go [] = [[]]
  go [[]] = []
  go ([] : _) = []
  go ((x : xs') : ys) = ((x :) <$> go ys) ++ go (xs' : ys)

  assert b x = if b x then x else error "allCombinations: assertion violation"

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
  verifyRule _ d@(Derivation f@(Unparsed{}) r) =
    Derivation f $ ParsedInvalid (getText r) "Parse error in formula." (fromWrapper r)
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
              -- Right formMap -> ParsedInvalid ruleText (prettyPrint formMap) ra
              Right formMap -> ParsedValid ruleText ra
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
    checkExistence rules = case rules !? ruleName of
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
            <> show expected
      Just (actual', expected') -> Right (actual', expected')
    ---------------------------------------------------

    ---------------------------------------------------
    -- 3. Unify references
    handleFormula :: Int -> Formula -> FormulaSpec -> Either Text (Formula, FormulaSpec)
    handleFormula line f fSpec = case unifyAlphaEq f fSpec of
      Nothing ->
        Left $
          "Found "
            <> show f
            <> " at line "
            <> show line
            <> ".\nBut expected a formula of the form "
            <> show fSpec
            <> "."
      Just (f', fSpec') -> Right (f', fSpec')
    handleAssumption :: Int -> Assumption -> FormulaSpec -> Either Text (Formula, FormulaSpec)
    handleAssumption line fw fSpec = case fw of
      Unparsed{} -> Left "Unparsed assumption --- INTERNAL ERROR SHOULD NOT HAPPEN"
      (ParsedInvalid txt err f) -> do
        (f', fSpec') <- handleFormula line f fSpec
        pure (f', fSpec')
      (ParsedValid txt f) -> do
        (f', fSpec') <- handleFormula line f fSpec
        pure (f', fSpec')
    unifyReferences :: Int -> RuleSpec -> [Reference] -> Either Text [(Formula, FormulaSpec)]
    unifyReferences n (RuleSpec (fSpec : fSpecs) pSpecs cSpec) (LineReference refLine : refs) = do
      f <- lookupReference refLine p
      f' <- handleFormula refLine f fSpec
      fs <- unifyReferences (n + 1) (RuleSpec fSpecs pSpecs cSpec) refs
      pure (f' : fs)
    unifyReferences n (RuleSpec [] (pSpec : pSpecs) cSpec) (ProofReference start end : refs) =
      case pIndexProof start end p of
        Nothing ->
          Left $
            "Line range "
              <> show start
              <> "-"
              <> show end
              <> " does not correspond to a subproof.\nLine "
              <> show start
              <> " should mark the start of a subproof and line "
              <> show end
              <> " should be its conclusion."
        Just prf -> do
          case (fromLineNo ruleLine p, fromLineRange start end p) of
            (Nothing, _) -> Left $ "Line " <> show ruleLine <> " is not a valid line. INTERNAL ERROR, SHOULD NOT HAPPEN"
            (_, Nothing) ->
              Left $
                "Line range "
                  <> show start
                  <> "-"
                  <> show end
                  <> " is not a valid range. INTERNAL ERROR, SHOULD NOT HAPPEN"
            (Just ruleAddr, Just refAddr) -> case refIsVisible start ruleAddr refAddr of
              Nothing -> Right ()
              Just err -> Left err
          fs <- handleProof (start, end) prf pSpec
          fs' <- unifyReferences (n + 1) (RuleSpec [] pSpecs cSpec) refs
          pure (fs ++ fs')
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
                      pure (s + 1, (a', fSpec'))
                  )
                  start
                  (zip fs fSpecs)
            (c', cSpec') <- handleAssumption end c cSpec
            pure (zip (fs' ++ [c']) (fSpecs' ++ [cSpec']))
      handleProof _ (ProofLine{}) _ = Left "handleProof found ProofLine -- SHOULD NOT HAPPEN - INTERNAL ERROR."
    unifyReferences n (RuleSpec (_ : _) _ _) (ProofReference start end : refs) =
      Left $
        "Rule ("
          <> ruleName
          <> ") expects a single line at position "
          <> show n
          <> " but got the range "
          <> show start
          <> "-"
          <> show end
          <> "."
    unifyReferences n (RuleSpec _ (_ : _) _) (LineReference line : refs) =
      Left $
        "Rule ("
          <> ruleName
          <> ") expects a line range at position "
          <> show n
          <> " but got the single line "
          <> show line
          <> "."
    unifyReferences n (RuleSpec (_ : fs) ps _) [] =
      Left $
        "Rule ("
          <> ruleName
          <> ") expects "
          <> show (n + length fs + length ps + 1)
          <> " references,\nbut got "
          <> show n
          <> " references."
    unifyReferences n (RuleSpec [] (_ : ps) _) [] =
      Left $
        "Rule ("
          <> ruleName
          <> ") expects "
          <> show (n + length ps + 1)
          <> " references,\nbut got "
          <> show n
          <> " references."
    unifyReferences n (RuleSpec [] [] _) (_ : refs) =
      Left $
        "Rule ("
          <> ruleName
          <> ") expects "
          <> show n
          <> " references,\nbut got "
          <> show (n + length refs + 1)
          <> " references."
    unifyReferences _ (RuleSpec [] [] _) [] = Right []
    ---------------------------------------------------

    ---------------------------------------------------
    -- 4. Collect terms
    collectTerms :: [(Formula, FormulaSpec)] -> Map Name [Term]
    collectTerms ((Pred _ ps, FPred _ qs) : rest) =
      M.unionWith
        (++)
        (collectTerms' (zip ps qs))
        (collectTerms rest)
     where
      collectTerms' :: [(Term, TermSpec)] -> Map Name [Term]
      collectTerms' [] = mempty
      collectTerms' ((Fun _ ts, TFun _ ss) : rest) = collectTerms' (zip ts ss ++ rest)
      collectTerms' ((t, TPlaceholder n) : rest) =
        insertWith
          (++)
          n
          [t]
          (collectTerms' rest)
      collectTerms' (_ : rest) = collectTerms' rest
    collectTerms ((Opr _ fs, FOpr _ fs') : rest) =
      collectTerms (zip fs fs' ++ rest)
    collectTerms ((Quantifier _ _ f, FQuantifier _ _ f') : rest) =
      collectTerms ((f, f') : rest)
    collectTerms ((FreshVar m, FFreshVar n) : rest) = insertWith (++) n [Var m] $ collectTerms rest
    collectTerms (_ : rest) = collectTerms rest
    collectTerms [] = mempty
    ---------------------------------------------------

    ---------------------------------------------------
    -- 5. Verify term mappings
    verifyTerms :: Map Name [Term] -> Either Text (Map Name Term)
    verifyTerms m = fromList <$> mapM makeUnique (toPairs m)
     where
      makeUnique :: (Name, [Term]) -> Either Text (Name, Term)
      makeUnique (_, []) = Left "INTERNAL ERROR, makeUnique got empty list of Terms!"
      makeUnique (v, t : ts) = do
        foldlM
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
                      <> show lastTerm
                      <> " and\n"
                      <> v
                      <> "↦"
                      <> show currTerm
                      <> "."
          )
          t
          ts
        pure (v, t)
    ---------------------------------------------------

    ---------------------------------------------------
    -- 6. Collect formula mappings using backward substitution
    verifyFormulae :: Map Name Term -> [(Formula, FormulaSpec)] -> Either Text (Map Name Formula)
    verifyFormulae termMap formsAndSpecs = do
      formMap <- reduceFormulae $ M.map (Left <$>) $ collectSimpleFormulae formsAndSpecs
      formMap' <- collectMoreFormulae formMap formsAndSpecs
      -- Left $ prettyPrint formMap'
      reduceFormulae formMap'
     where
      collectSimpleFormulae :: [(Formula, FormulaSpec)] -> Map Name (NonEmpty Formula)
      collectSimpleFormulae [] = mempty
      collectSimpleFormulae ((Pred{}, FPred{}) : rest) = collectSimpleFormulae rest
      collectSimpleFormulae ((Opr _ fs, FOpr _ fSpecs) : rest) = collectSimpleFormulae $ zip fs fSpecs <> rest
      collectSimpleFormulae ((Quantifier _ _ f, FQuantifier _ _ fSpec) : rest) = collectSimpleFormulae $ (f, fSpec) : rest
      collectSimpleFormulae ((FreshVar n, FFreshVar m) : rest) = collectSimpleFormulae rest
      collectSimpleFormulae ((f, FPlaceholder n) : rest) = insertWith (<>) n (f :| []) $ collectSimpleFormulae rest
      collectSimpleFormulae (_ : rest) = collectSimpleFormulae rest
      reduceFormulae :: Map Name (NonEmpty (Either Formula [Formula])) -> Either Text (Map Name Formula)
      reduceFormulae = M.traverseWithKey reduceHelper
       where
        reduceHelper :: Name -> NonEmpty (Either Formula [Formula]) -> Either Text Formula
        reduceHelper n (Left f :| rest) = go n f rest
        reduceHelper n (Right [] :| rest) = Left "reduceHelper: can't find match!"
        -- reduceHelper n (Right fs :| rest) = Left $ "reduceHelper: can't find match!" <> show fs)
        reduceHelper n (Right (f : fs) :| rest) = case go n f rest of
          Left err -> reduceHelper n (Right fs :| rest)
          Right f -> Right f
        go :: Name -> Formula -> [Either Formula [Formula]] -> Either Text Formula
        go n f [] = Right f
        go n f (Left f' : rest) = if f == f' then go n f' rest else Left "reduceFormulae: f/=f'" -- TODO error message
        go n f (Right fs' : rest) = mapFs fs'
         where
          mapFs :: [Formula] -> Either Text Formula
          mapFs [] = Left $ "reduceFormulae: can't find match for f=" <> show f
          mapFs (f' : fs) = if f /= f' then mapFs fs else Right f'

      collectMoreFormulae ::
        Map Name Formula ->
        [(Formula, FormulaSpec)] ->
        Either Text (Map Name (NonEmpty (Either Formula [Formula])))
      collectMoreFormulae formMap [] = Right . M.map (\f -> Left f :| []) $ formMap
      collectMoreFormulae formMap ((f, FSubst phi (Subst n t)) : rest) = case formMap !? phi of
        -- unify fs
        Just phiF -> case unifyFormulaeOnVariable n [(phiF, f)] of
          Nothing -> Left $ "Error unifying " <> show phiF <> " with\n" <> show f
          -- compare assignment of E
          Just mgu -> case (mgu !? n, termMap !? n) of
            ((Nothing, _); (_, Nothing)) -> insertWith (<>) phi (Left phiF :| []) <$> collectMoreFormulae formMap rest
            (Just e, Just e') ->
              if e == e'
                then insertWith (<>) phi (Left phiF :| []) <$> collectMoreFormulae formMap rest
                else Left "Found different assignments for E"
        Nothing -> case t of
          TPlaceholder e -> case termMap !? e of
            Nothing -> Left "Term has wrong form, RULEERROR!" -- error
            -- backwards
            Just t' -> case substBackwardsForm (Subst n t') f of
              l@(_ : _ : _) ->
                insertWith
                  (<>)
                  phi
                  (Right l :| [])
                  <$> collectMoreFormulae formMap rest
              _ -> Left $ "backwards substituting " <> prettyPrint f <> " failed."
          _ -> Left "Term has wrong form, RULEERROR!" -- error
      collectMoreFormulae formMap (_ : rest) = collectMoreFormulae formMap rest
      substBackwardsForm :: Subst Term -> Formula -> [Formula]
      substBackwardsForm s (Pred p ts) = map (Pred p) . allCombinations $ map (substBackwardsTerm s) ts
      substBackwardsForm s (Opr o fs) = map (Opr o) . allCombinations $ map (substBackwardsForm s) fs
      -- TODO need freshness here :(
      substBackwardsForm s@(Subst n t) (Quantifier q v f) =
        if n == v
          then undefined
          else map (Quantifier q v) (substBackwardsForm s f)
      substBackwardsForm _ f = error "tried substBackwardsForm on FreshVar"
      substBackwardsTerm :: Subst Term -> Term -> [Term]
      substBackwardsTerm s@(Subst n e) t | t == e = [Var n, t]
      substBackwardsTerm s (Var x) = [Var x]
      substBackwardsTerm s (Fun f ts) | not (null ts) = map (Fun f) . allCombinations $ map (substBackwardsTerm s) ts
    ---------------------------------------------------

    -- helpers
    refIsVisible :: Int -> NodeAddr -> NodeAddr -> Maybe Text
    refIsVisible line ruleAddr refAddr
      | ruleAddr <= refAddr = Just "Can only reference lines that appear before this line!"
    refIsVisible line (NAProof n (Just na1)) (NAProof m (Just na2))
      | n == m = refIsVisible line na1 na2
    refIsVisible line rua ra@(NAProof _ (Just _)) =
      Just "Line cannot be referenced because it is located inside of a subproof."
    refIsVisible _ _ _ = Nothing

    lookupReference :: Int -> Proof -> Either Text Formula
    lookupReference refLine p
      | ruleLine < refLine =
          Left $
            "Line "
              <> show refLine
              <> " can not be referenced because it appears after this line."
      | ruleLine == refLine =
          Left "Can not reference the same line."
    lookupReference refLine p = case (fromLineNo ruleLine p, fromLineNo refLine p) of
      (Nothing, _) -> Left $ "Line " <> show ruleLine <> " is not a valid line. INTERNAL ERROR, SHOULD NOT HAPPEN"
      (_, Nothing) -> Left $ "Line " <> show refLine <> " is not a valid line. INTERNAL ERROR, SHOULD NOT HAPPEN"
      (Just ruleAddr, Just refAddr) ->
        maybe
          ( case pIndex refLine p of
              Nothing -> Left $ "Line " <> show refLine <> " is not a valid line."
              Just (Left (ParsedValid _ f)) -> Right f
              Just (Right (Derivation (ParsedValid _ f) _)) -> Right f
              Just _ -> Left $ "Parse error in line: " <> show refLine
          )
          Left
          (refIsVisible refLine ruleAddr refAddr)