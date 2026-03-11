{- |
Module      : Fitch.Verification
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module implements the proof verification algorithm for Fitch-style
natural deduction t'Proof's. Given a map of t'RuleSpec's, it checks each
t'Derivation' line by verifying that its t'RuleApplication' is applied correctly.

Phases of proof verification:

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
     `Map Name [Either RawFormula [RawFormula]]`, where
     `Name` is e.g. φ, `RawFormula` is a formula that has been identified as φ,
     and `[RawFormula]` is a list of possible formulae that
     can be identified as φ (yielded by backwards-substitution).
  7. Now check that for every φ all its mappings can be made equal by
     choosing from the lists.

It also provides 'checkFreshness' for validating fresh-variable
t'Assumption's, and 'regenerateSymbols' for collecting and validating
function- and predicate-symbol arities across the whole t'Proof'.
-}
module Fitch.Verification where

import App.Model
import Data.Map qualified as M
import Data.Traversable (mapAccumM)
import Fitch.Proof
import Fitch.Unification
import Relude.Extra.Map
import Relude.Extra.Newtype
import Specification.Types
import Util (allCombinations)

{- | Runs the full proof-verification pipeline on a t'Proof',
adding error messages to erroneous t'RuleApplication's

__Note:__ This does not check freshness assumptions or check if arities are consistent.
Use 'checkFreshness' and 'regenerateSymbols' for that.
-}
verifyProof :: Map Name RuleSpec -> Proof -> Proof
verifyProof rules p = pMapLinesWithLineNo (const id) verifyRule p
 where
  verifyRule :: Int -> Derivation -> Derivation
  verifyRule _ d@(Derivation _ (Unparsed{})) = d
  verifyRule _ d@(Derivation f@(Unparsed{}) wr) =
    let (ruleText, ra) = case wr of
          (ParsedInvalid ruleText _ ra) -> (ruleText, ra)
          (ParsedValid ruleText ra) -> (ruleText, ra)
     in Derivation f $ ParsedInvalid ruleText "Parse error in formula." ra
  verifyRule ruleLine (Derivation wf wr) = Derivation wf
    $ either
      (\err -> ParsedInvalid ruleText err ra)
      (const $ ParsedValid ruleText ra)
    $ do
      spec <- checkExistence rules
      (conclusion, conclusionSpec) <- checkConclusion spec formula
      formulaSpecs <- unifyReferences 0 spec refs
      termMap <-
        verifyTerms (collectTermsFormula (Right (conclusion, conclusionSpec) : formulaSpecs))
      formMap <- verifyFormulae termMap (Right (conclusion, conclusionSpec) : formulaSpecs)
      pass
   where
    (formulaText, formula, ruleText, ra@(RuleApplication ruleName refs)) = case (wf, wr) of
      (ParsedInvalid formulaText _ f, ParsedInvalid ruleText _ ra) -> (formulaText, f, ruleText, ra)
      (ParsedValid formulaText f, ParsedInvalid ruleText _ ra) -> (formulaText, f, ruleText, ra)
      (ParsedInvalid formulaText _ f, ParsedValid ruleText ra) -> (formulaText, f, ruleText, ra)
      (ParsedValid formulaText f, ParsedValid ruleText ra) -> (formulaText, f, ruleText, ra)
    ---------------------------------------------------
    -- 1. Check that the rule exists.
    checkExistence :: Map Name RuleSpec -> Either Text RuleSpec
    checkExistence rules = case rules !? ruleName of
      Nothing -> Left ("Rule (" <> ruleName <> ") does not exist.")
      Just spec -> Right spec
    ---------------------------------------------------

    ---------------------------------------------------
    -- 2. Unify conclusion.
    checkConclusion :: RuleSpec -> RawFormula -> Either Text (RawFormula, FormulaSpec)
    checkConclusion (RuleSpec _ _ expected) actual =
      if formulaMatchesSpec actual expected
        then Right (actual, expected)
        else
          Left $
            "Rule cannot be applied to "
              <> formulaText
              <> "\nExpecting a formula of the form "
              <> prettyPrint expected
    ---------------------------------------------------

    ---------------------------------------------------
    -- 3. Unify references
    handleFormula :: Int -> Formula -> FormulaSpec -> Either Text (RawFormula, FormulaSpec)
    handleFormula line f fSpec = case f of
      Unparsed{} -> Left $ "Unparsed formula at line " <> show line
      ParsedInvalid txt err rf -> handleRawFormula rf
      ParsedValid txt rf -> handleRawFormula rf
     where
      handleRawFormula :: RawFormula -> Either Text (RawFormula, FormulaSpec)
      handleRawFormula rf =
        if formulaMatchesSpec rf fSpec
          then Right (rf, fSpec)
          else
            Left $
              "Found "
                <> prettyPrint rf
                <> " at line "
                <> show line
                <> ".\nBut expected a formula of the form "
                <> prettyPrint fSpec
                <> "."
    handleAssumption ::
      Int -> Assumption -> AssumptionSpec -> Either Text (RawAssumption, AssumptionSpec)
    handleAssumption line (a, _) aSpec = case a of
      Unparsed{} -> Left $ "Unparsed assumption at line " <> show line
      (ParsedInvalid txt err ra) -> handleRawAssumption ra
      (ParsedValid txt ra) -> handleRawAssumption ra
     where
      handleRawAssumption :: RawAssumption -> Either Text (RawAssumption, AssumptionSpec)
      handleRawAssumption ra =
        if assumptionMatchesSpec ra aSpec
          then Right (ra, aSpec)
          else
            Left $
              "Found "
                <> prettyPrint ra
                <> " at line "
                <> show line
                <> ".\nBut expected a formula of the form "
                <> prettyPrint aSpec
                <> "."
    unifyReferences ::
      Int ->
      RuleSpec ->
      [Reference] ->
      Either Text [Either (RawAssumption, AssumptionSpec) (RawFormula, FormulaSpec)]
    unifyReferences n (RuleSpec (fSpec : fSpecs) pSpecs cSpec) (LineReference refLine : refs) = do
      f <- lookupLineReference refLine p
      f' <- case f of
        Left a -> Left <$> handleAssumption refLine a (AssumptionSpec fSpec)
        Right f -> Right <$> handleFormula refLine f fSpec
      fs <- unifyReferences (n + 1) (RuleSpec fSpecs pSpecs cSpec) refs
      pure (f' : fs)
    unifyReferences n (RuleSpec [] (pSpec : pSpecs) cSpec) (ProofReference start end : refs) = do
      prf <- lookupProofReference start end p
      fs <- handleProof (start, end) prf pSpec
      fs' <- unifyReferences (n + 1) (RuleSpec [] pSpecs cSpec) refs
      pure (fs <> fs')
     where
      handleProof ::
        (Int, Int) ->
        Proof ->
        ProofSpec ->
        Either Text [Either (RawAssumption, AssumptionSpec) (RawFormula, FormulaSpec)]
      handleProof (start, end) (SubProof fs ps (Derivation c r)) (fSpecs, cSpec)
        | length fs /= length fSpecs =
            Left
              "Number of assumptions of the subproof does not match the expected number."
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
            (c', cSpec') <- handleFormula end c cSpec
            pure $ zipWith (curry Left) fs' fSpecs' <> [Right (c', cSpec')]
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
    collectTermsTerm :: [(Term, TermSpec)] -> Map Name [Term]
    collectTermsTerm [] = mempty
    collectTermsTerm ((Fun _ ts, TFun _ ss) : rest) = collectTermsTerm (zip ts ss <> rest)
    collectTermsTerm ((t, TPlaceholder n) : rest) =
      insertWith
        (<>)
        n
        [t]
        (collectTermsTerm rest)
    collectTermsTerm (_ : rest) = collectTermsTerm rest

    collectTermsFormula ::
      [Either (RawAssumption, AssumptionSpec) (RawFormula, FormulaSpec)] -> Map Name [Term]
    collectTermsFormula (Right (Pred _ [p1, p2], FInfixPred _ q1 q2) : rest) =
      M.unionWith
        (<>)
        (collectTermsTerm [(p1, q1), (p2, q2)])
        (collectTermsFormula rest)
    collectTermsFormula (Right (Pred _ ps, FPred _ qs) : rest) =
      M.unionWith
        (<>)
        (collectTermsTerm (zip ps qs))
        (collectTermsFormula rest)
    collectTermsFormula (Right (Opr _ fs, FOpr _ fs') : rest) =
      collectTermsFormula (zipWith (curry Right) fs fs' <> rest)
    collectTermsFormula (Right (Quantifier _ v f, FQuantifier _ v' f') : rest) =
      insertWith
        (<>)
        v'
        [Var v]
        (collectTermsFormula (Right (f, f') : rest))
    collectTermsFormula (Left (FreshVar m, FFreshVar n) : rest) = insertWith (<>) n [Var m] $ collectTermsFormula rest
    collectTermsFormula (Left (RawAssumption f, AssumptionSpec fSpec) : rest) = collectTermsFormula (Right (f, fSpec) : rest)
    collectTermsFormula (_ : rest) = collectTermsFormula rest
    collectTermsFormula [] = mempty
    ---------------------------------------------------

    ---------------------------------------------------
    -- 5. Verify term mappings
    verifyTerms :: Map Name [Term] -> Either Text (Map Name Term)
    verifyTerms m = fromList <$> mapM makeUnique (toPairs m)
     where
      makeUnique :: (Name, [Term]) -> Either Text (Name, Term)
      makeUnique (_, []) = Left "Internal error on makeUnique: should not happen!"
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
                      <> prettyPrint lastTerm
                      <> " and\n"
                      <> v
                      <> "↦"
                      <> prettyPrint currTerm
                      <> "."
          )
          t
          ts
        pure (v, t)
    ---------------------------------------------------

    ---------------------------------------------------
    -- 6. Collect formula mappings using backward substitution
    verifyFormulae ::
      Map Name Term ->
      [Either (RawAssumption, AssumptionSpec) (RawFormula, FormulaSpec)] ->
      Either Text (Map Name RawFormula)
    verifyFormulae termMap formsAndSpecs = do
      formMap <- reduceFormulae $ M.map (Left <$>) $ collectSimpleFormulae formsAndSpecs
      formMap' <- collectMoreFormulae formMap formsAndSpecs
      reduceFormulae (fmap toList <<$>> formMap')
     where
      collectSimpleFormulae ::
        [Either (RawAssumption, AssumptionSpec) (RawFormula, FormulaSpec)] ->
        Map Name (NonEmpty RawFormula)
      collectSimpleFormulae [] = mempty
      collectSimpleFormulae (Right (Pred{}, (FPred{}; FInfixPred{})) : rest) =
        collectSimpleFormulae rest
      collectSimpleFormulae (Right (Opr _ fs, FOpr _ fSpecs) : rest) =
        collectSimpleFormulae $ zipWith (curry Right) fs fSpecs <> rest
      collectSimpleFormulae (Right (Quantifier _ _ f, FQuantifier _ _ fSpec) : rest) =
        collectSimpleFormulae $ Right (f, fSpec) : rest
      collectSimpleFormulae (Left (FreshVar n, FFreshVar m) : rest) =
        collectSimpleFormulae rest
      collectSimpleFormulae (Left (RawAssumption f, AssumptionSpec fSpec) : rest) =
        collectSimpleFormulae (Right (f, fSpec) : rest)
      collectSimpleFormulae (Right (f, FPlaceholder n) : rest) =
        insertWith
          (<>)
          n
          (f :| [])
          $ collectSimpleFormulae rest
      collectSimpleFormulae (_ : rest) = collectSimpleFormulae rest
      reduceFormulae ::
        Map Name (NonEmpty (Either RawFormula [RawFormula])) ->
        Either Text (Map Name RawFormula)
      reduceFormulae = M.traverseWithKey reduceHelper
       where
        reduceHelper ::
          Name -> NonEmpty (Either RawFormula [RawFormula]) -> Either Text RawFormula
        reduceHelper n (Left f :| rest) = go n f rest
        reduceHelper n (Right [] :| rest) = Left "Could not find match for formula."
        reduceHelper n (Right [f] :| rest) = case go n f rest of
          Left err -> Left $ "Error, can't find match for " <> prettyPrint f
          Right f -> Right f
        reduceHelper n (Right (f : fs) :| rest) = case go n f rest of
          Left err -> reduceHelper n (Right fs :| rest)
          Right f -> Right f
        go :: Name -> RawFormula -> [Either RawFormula [RawFormula]] -> Either Text RawFormula
        go n f [] = Right f
        go n f (Left f' : rest) =
          if f == f'
            then
              go n f' rest
            else
              Left $
                "Error, formulae:\n" <> prettyPrint f <> "\n" <> prettyPrint f' <> "\nDo not match."
        go n f (Right fs' : rest) = mapFs fs'
         where
          mapFs :: [RawFormula] -> Either Text RawFormula
          mapFs [] = Left $ "Error, can't find match for formula:\n" <> prettyPrint f
          mapFs (f' : fs) = if f /= f' then mapFs fs else Right f'

      collectMoreFormulae ::
        Map Name RawFormula ->
        [Either (RawAssumption, AssumptionSpec) (RawFormula, FormulaSpec)] ->
        Either Text (Map Name (NonEmpty (Either RawFormula (NonEmpty RawFormula))))
      collectMoreFormulae formMap [] = Right . M.map (\f -> Left f :| []) $ formMap
      collectMoreFormulae formMap (Left (RawAssumption f, AssumptionSpec fSpec) : rest) =
        collectMoreFormulae formMap (Right (f, fSpec) : rest)
      collectMoreFormulae formMap (Right (f, FSubst phi (Subst x t)) : rest) = case formMap !? phi of
        -- unify fs
        Just phiF ->
          let x' = case termMap !? x of
                Just (Var x') -> x'
                _ -> "_" <> x
           in case unifyFormulaeOnVariable x' [(phiF, f)] of
                Nothing ->
                  Left $
                    "Error unifying "
                      <> prettyPrint phiF
                      <> " with\n"
                      <> prettyPrint f
                      <> "\non variable "
                      <> x'
                      <> "."
                -- compare assignment of E
                Just mgu -> case (mgu !? x', termMap !? t) of
                  _
                    | size mgu > 1 ->
                        Left $ "Error unifying " <> prettyPrint phiF <> " with\n" <> prettyPrint f
                  ((Nothing, _); (_, Nothing)) ->
                    insertWith
                      (<>)
                      phi
                      (Left phiF :| [])
                      <$> collectMoreFormulae formMap rest
                  (Just e, Just e') ->
                    if e == e'
                      then insertWith (<>) phi (Left phiF :| []) <$> collectMoreFormulae formMap rest
                      else
                        Left $
                          "Found different assignments for "
                            <> x'
                            <> ":\n"
                            <> prettyPrint e
                            <> "\nand\n"
                            <> prettyPrint e'
        Nothing -> case termMap !? t of
          -- TODO better error message
          Nothing ->
            Left $ "Term has wrong form, can't find " <> t <> " in termMap=\n" <> prettyPrint termMap -- error
            -- backwards
          Just t' ->
            let x' = case termMap !? x of
                  Just (Var x') -> x'
                  _ -> "_" <> x
             in -- NOTE: we use ('_' <> x) because it can not clash with a variable name.
                case substBackwardsForm (Subst x' t') f of
                  f :| [] ->
                    insertWith
                      (<>)
                      phi
                      (Left f :| [])
                      <$> collectMoreFormulae formMap rest
                  l@(_ :| _ : _) ->
                    insertWith
                      (<>)
                      phi
                      (Right l :| [])
                      <$> collectMoreFormulae formMap rest
      collectMoreFormulae formMap (_ : rest) = collectMoreFormulae formMap rest
      substBackwardsForm :: Subst Term -> RawFormula -> NonEmpty RawFormula
      substBackwardsForm s (InfixPred p t1 t2) =
        fmap (Pred p) . allCombinations $ fmap (substBackwardsTerm s) [t1, t2]
      substBackwardsForm s (Pred p ts) =
        fmap (Pred p) . allCombinations $ fmap (substBackwardsTerm s) ts
      substBackwardsForm s (Opr o fs) =
        fmap (Opr o) . allCombinations $ fmap (substBackwardsForm s) fs
      -- NOTE: @x == v@ is not possible, because we only backwardsubst if @E@ is assigned and in
      -- this case there is no rule where @x@ is assigned.
      -- Thus @v@ here will be something like '_x' that does not occur naturally, i.e. not in Subst!
      substBackwardsForm s@(Subst x t) (Quantifier q v f) =
        fmap (Quantifier q v) (substBackwardsForm s f)
      substBackwardsTerm :: Subst Term -> Term -> NonEmpty Term
      substBackwardsTerm s@(Subst n e) t | t == e = [Var n, t]
      substBackwardsTerm s (Var x) = one $ Var x
      substBackwardsTerm s (Fun f ts) =
        fmap (Fun f) . allCombinations . toList $ fmap (substBackwardsTerm s) ts
    ---------------------------------------------------

    -- helpers

    -- Checks if given reference is visible for the current rule.
    refIsVisible ::
      (Int, NodeAddr) -> Either (Int, NodeAddr) ((Int, Int), ProofAddr) -> Maybe Text
    refIsVisible (ruleLine, ruleAddr) (Left (refLine, refAddr))
      | ruleLine <= refLine =
          Just $
            "Line "
              <> show refLine
              <> " can not be referenced, because it does not appear before line "
              <> show ruleLine
              <> "!"
    refIsVisible (ruleLine, ruleAddr) (Right ((start, end), refAddr))
      | ruleLine < start =
          Just $
            "Line range "
              <> show start
              <> "-"
              <> show end
              <> " can not be referenced, because it does not appear before line "
              <> show ruleLine
              <> "!"
    refIsVisible (ruleLine, NAProof n na1) (Left (line, NAProof m na2))
      | n == m = refIsVisible (ruleLine, na1) (Left (line, na2))
    refIsVisible (ruleLine, NAProof n na1) (Right ((start, end), PANested m pa2))
      | n == m = refIsVisible (ruleLine, na1) (Right ((start, end), pa2))
    refIsVisible _ (Left (line, NAProof _ _)) =
      Just $
        "Line "
          <> show line
          <> " cannot be referenced because it is located inside of a subproof."
    refIsVisible (ruleLine, ruleAddr) (Right ((start, end), naContainedIn ruleAddr -> True)) =
      Just $
        "Line range "
          <> show start
          <> "-"
          <> show end
          <> " can not be referenced, because it contains line "
          <> show ruleLine
          <> "!"
    refIsVisible _ (Right ((start, end), PANested _ _)) =
      Just $
        "Line range "
          <> show start
          <> "-"
          <> show end
          <> " cannot be referenced because it is located inside of a subproof."
    refIsVisible _ _ = Nothing

    -- tries to look up a 'ProofReference'
    lookupProofReference :: Int -> Int -> Proof -> Either Text Proof
    lookupProofReference start end p = case (pIndexProof start end p, fromLineRange start end p, fromLineNo ruleLine p) of
      (_, _, Nothing) -> Left "Internal error on lookupProofReference: should not happen!"
      ((Nothing, _, _); (_, Nothing, _)) ->
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
      (Just prf, Just refAddr, Just ruleAddr) -> case refIsVisible (ruleLine, ruleAddr) (Right ((start, end), refAddr)) of
        Nothing -> Right prf
        Just err -> Left err

    -- tries to look up a 'LineReference'
    lookupLineReference :: Int -> Proof -> Either Text (Either Assumption Formula)
    lookupLineReference refLine p = case (pIndex refLine p, fromLineNo refLine p, fromLineNo ruleLine p) of
      (_, _, Nothing) -> Left "Internal error on lookupLineReference: should not happen!"
      ((Nothing, _, _); (_, Nothing, _)) ->
        Left $
          "Can not reference line "
            <> show refLine
            <> " because it does not exist."
      (Just (Left a), Just refAddr, Just ruleAddr) -> maybeToLeft (Left a) (refIsVisible (ruleLine, ruleAddr) (Left (refLine, refAddr)))
      (Just (Right (Derivation f _)), Just refAddr, Just ruleAddr) -> maybeToLeft (Right f) (refIsVisible (ruleLine, ruleAddr) (Left (refLine, refAddr)))

-- * Semantic checking

{- | Validates every fresh-variable t'Assumption' @[c]@ in a t'Proof'.

For each such t'Assumption', it collects all lines that are in scope and
checks that @c@ does not appear free in any of their t'Formula'e.
-}
checkFreshness :: Proof -> Proof
checkFreshness p = pMapLinesWithAddr (goAssumption p) (const id) p
 where
  goAssumption :: Proof -> NodeAddr -> Assumption -> Assumption
  goAssumption _ _ a@(Unparsed{}, _) = a
  goAssumption p na a@(ParsedInvalid txt _ ra, r) = (goRawAssumption p na txt ra, r)
  goAssumption p na a@(ParsedValid txt ra, r) = (goRawAssumption p na txt ra, r)
  goRawAssumption :: Proof -> NodeAddr -> Text -> RawAssumption -> Wrapper RawAssumption
  goRawAssumption p (pCollectFreshnessNodes p -> nodes) txt ra@(FreshVar v) =
    case isFreshList v nodes of
      Nothing -> ParsedValid txt ra
      Just (naf', f') ->
        ParsedInvalid
          txt
          ( "Could not verify freshness of "
              <> v
              <> "\nIt appears in formula:\n"
              <> show (lineNoOr999 naf' p)
              <> "|"
              <> prettyPrint f'
          )
          ra
  goRawAssumption _ _ txt ra = ParsedValid txt ra
  isFreshList ::
    Name ->
    [(NodeAddr, Either Assumption Derivation)] ->
    Maybe (NodeAddr, Either RawAssumption RawFormula)
  isFreshList v [] = Nothing
  isFreshList v ((na, Left (fromWrapper -> Nothing, _)) : rest) = isFreshList v rest
  isFreshList v ((na, Left (fromWrapper -> Just a, _)) : rest) = if isFresh v a then isFreshList v rest else Just (na, Left a)
  isFreshList v ((na, Right (Derivation (fromWrapper -> Nothing) _)) : rest) = isFreshList v rest
  isFreshList v ((na, Right (Derivation (fromWrapper -> Just f) _)) : rest) = if isFresh v f then isFreshList v rest else Just (na, Right f)

type RegenState = (Int, Map Text (Int, Pos), Map Text (Int, Pos))

{- | Recalculates the list of functionsymbols and predicatesymbols in the model.

This is done by iterating over the proof and collecting all symbols.
The first occurence of a symbol fixes its arity, and all following symbols with the same t'Name' are compared to this arity.
-}
regenerateSymbols :: Proof -> (Map Text (Int, Pos), Map Text (Int, Pos), Proof)
regenerateSymbols p =
  let
    ((_, fsymbs, psymbs), p') = pMapLinesAccumL goAssumption goLine (1, mempty, mempty) p
   in
    (fsymbs, psymbs, p')
 where
  goAssumption :: RegenState -> Assumption -> (RegenState, Assumption)
  goAssumption (n, fsymbs, psymbs) a@(Unparsed{}, _) =
    ((n + 1, fsymbs, psymbs), a)
  goAssumption (n, fsymbs, psymbs) a@(ParsedInvalid txt err (RawAssumption f), r) =
    let ((n', fsymbs', psymbs'), f') = goFormula (n, fsymbs, psymbs) (ParsedInvalid txt err f)
     in ((n', fsymbs', psymbs'), (RawAssumption <$> f', r))
  goAssumption (n, fsymbs, psymbs) a@(ParsedValid txt (RawAssumption f), r) =
    let ((n', fsymbs', psymbs'), f') = goFormula (n, fsymbs, psymbs) (ParsedValid txt f)
     in ((n', fsymbs', psymbs'), (RawAssumption <$> f', r))
  goAssumption (n, fsymbs, psymbs) a@(ParsedInvalid _ _ (FreshVar{}), _) =
    ((n + 1, fsymbs, psymbs), a)
  goAssumption (n, fsymbs, psymbs) a@(ParsedValid _ (FreshVar{}), _) =
    ((n + 1, fsymbs, psymbs), a)

  -- collect symbols inside a formula
  goFormula :: RegenState -> Formula -> (RegenState, Formula)
  -- skip unparsed formulae
  goFormula (n, fsymbs, psymbs) a@(Unparsed{}) = ((n + 1, fsymbs, psymbs), a)
  goFormula (n, fsymbs, psymbs) a =
    let
      (formula, txt) = case a of
        (ParsedInvalid txt _ f) -> (f, txt)
        (ParsedValid txt f) -> (f, txt)
      (fsymbs', psymbs', a') = go n fsymbs psymbs txt formula
     in
      ((n + 1, fsymbs', psymbs'), a')
   where
    goArgs :: Int -> Map Text (Int, Pos) -> [Term] -> Either Text (Map Text (Int, Pos))
    goArgs n = foldlM (\fsymbs' t -> goTerm n fsymbs' t)
     where
      goTerm :: Int -> Map Text (Int, Pos) -> Term -> Either Text (Map Text (Int, Pos))
      goTerm _ fsymbs (Var{}) = Right fsymbs
      goTerm n fsymbs (Fun name args) = do
        -- first check inner symbols
        fsymbs' <- goArgs n fsymbs args
        -- then check the function symbol
        case fsymbs' !? name of
          Nothing -> Right $ insert name (length args, n) fsymbs'
          Just (expLen, pos) ->
            if expLen == length args
              then Right fsymbs'
              else
                Left $
                  "Function symbol "
                    <> show name
                    <> " has "
                    <> show (length args)
                    <> " argument"
                    <> (if length args == 1 then "" else "s")
                    <> ",\nbut in line "
                    <> show pos
                    <> " it appears with "
                    <> show expLen
                    <> " argument"
                    <> (if expLen == 1 then "" else "s")
                    <> "."
    -- proccesses a single formula.
    go ::
      Int ->
      Map Text (Int, Pos) ->
      Map Text (Int, Pos) ->
      Text ->
      RawFormula ->
      (Map Text (Int, Pos), Map Text (Int, Pos), Formula)
    go n fsymbs psymbs txt formula@(Pred name args) =
      let
        -- first check function symbols
        mTermError = goArgs n fsymbs args
       in
        case mTermError of
          Left termError -> (fsymbs, psymbs, ParsedInvalid txt termError formula)
          -- then check the predicate symbol
          Right fsymbs' ->
            case psymbs !? name of
              Nothing ->
                let
                  psymbs' = insert name (length args, n) psymbs
                 in
                  (fsymbs', psymbs', ParsedValid txt formula)
              Just (expLen, pos) ->
                if expLen == length args
                  then (fsymbs', psymbs, ParsedValid txt formula)
                  else
                    ( fsymbs'
                    , psymbs
                    , ParsedInvalid
                        txt
                        ( "Predicate symbol "
                            <> name
                            <> " has "
                            <> show (length args)
                            <> " argument"
                            <> (if length args == 1 then "" else "s")
                            <> ",\nbut in line "
                            <> show pos
                            <> " it appears with "
                            <> show expLen
                            <> " argument"
                            <> (if expLen == 1 then "" else "s")
                            <> "."
                        )
                        formula
                    )
    go n fsymbs psymbs txt form@(Opr name fs) =
      foldlM (\r f -> go n fsymbs psymbs txt f <&> combineWrappers r) (ParsedValid txt form) fs
     where
      combineWrappers :: Wrapper RawFormula -> Wrapper RawFormula -> Wrapper RawFormula
      combineWrappers (Unparsed _ err) _ = Unparsed txt err
      combineWrappers (ParsedInvalid{}) (Unparsed _ err) = Unparsed txt err
      combineWrappers (ParsedInvalid _ err _) (ParsedInvalid{}) = ParsedInvalid txt err form
      combineWrappers (ParsedInvalid _ err _) (ParsedValid{}) = ParsedInvalid txt err form
      combineWrappers (ParsedValid{}) (Unparsed _ err) = Unparsed txt err
      combineWrappers (ParsedValid{}) (ParsedInvalid _ err _) = ParsedInvalid txt err form
      combineWrappers (ParsedValid{}) (ParsedValid{}) = ParsedValid txt form
    go n fsymbs psymbs txt (Quantifier name variable formula) = go n fsymbs psymbs txt formula <&> (Quantifier name variable <$>)
  -- proccesses a single line, by proccessing its formula.
  goLine :: RegenState -> Derivation -> (RegenState, Derivation)
  goLine (n, fsymbs, psymbs) (Derivation f r) =
    let
      ((n', fsymbs', psymbs'), f') = goFormula (n, fsymbs, psymbs) f
     in
      ((n', fsymbs', psymbs'), Derivation f' r)
