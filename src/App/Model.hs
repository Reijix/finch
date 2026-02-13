module App.Model where

import Fitch.Proof
import Fitch.Unification
import Miso (
  App,
  Attribute,
  DOMRef,
  Effect,
  KeyCode,
  KeyInfo,
  MisoString,
  PointerEvent (client),
  ROOT,
  View,
  consoleLog,
  io_,
  mouseSub,
  ms,
  onWithOptions,
  pointerDecoder,
  preventDefault,
  startApp,
  text,
 )
import Miso.CSS qualified as CSS
import Miso.Lens (Lens, lens, use, (%=), (.=), (<~))
import Miso.Svg.Element qualified as S
import Miso.Svg.Property qualified as SP
import Relude.Extra.Map (DynamicMap (insert), (!?))
import Relude.Extra.Newtype

-----------------------------------------------------------------------------

-- * Types

data DropLocation where
  LocationAddr :: NodeAddr -> DropLocation
  LocationBin :: DropLocation
  deriving (Show, Eq)

data SpawnType where
  SpawnLine :: SpawnType
  SpawnProof :: SpawnType
  deriving (Show, Eq)

data Action where
  Setup :: Action
  Blur :: Action
  Input :: MisoString -> DOMRef -> Action
  Change :: Action
  ProcessInput :: MisoString -> Int -> Int -> Either NodeAddr NodeAddr -> Action
  DoubleClick :: Either NodeAddr NodeAddr -> Action
  Drop :: DropLocation -> Action
  DragEnter :: NodeAddr -> Action
  DragLeave :: Action
  DragOver :: Action
  DragStart :: Either NodeAddr ProofAddr -> Action
  SpawnStart :: SpawnType -> Action
  DragEnd :: Action
  Drag :: Action
  Nop :: Action
  ProcessParens :: Either NodeAddr NodeAddr -> Int -> Int -> Action
  KeyDownStart :: Either NodeAddr NodeAddr -> DOMRef -> Action
  KeyDownStop :: Either NodeAddr NodeAddr -> Action

-----------------------------------------------------------------------------

type Pos = Int

data Model = Model
  { _focusedLine :: Maybe (Either NodeAddr NodeAddr)
  -- ^ the line that is currently focused
  , _proof :: Proof
  -- ^ the current proof
  , _dragTarget :: Maybe (Either NodeAddr ProofAddr)
  -- ^ the element that is currently being dragged
  , _spawnType :: Maybe SpawnType
  -- ^ the type of element that is currently being spawned
  , _currentHoverLine :: Maybe NodeAddr
  -- ^ the line before which the user currently hovers
  , _dragging :: Bool
  -- ^ denotes whether the user is currently dragging an element
  , _operators :: [(Text, Text, Int)]
  {- ^ list of operators, consisting of (alias, symbol, arity)
  where alias is an alternative notation for the symbol
  -}
  , _infixPreds :: [(Text, Text)]
  , _quantifiers :: [(Text, Text)]
  {- ^ list of quantifiers, consisting of (alias, symbol)
  where alias is an alternative notation for the symbol
  -}
  , _functionSymbols :: Map Text (Int, Pos)
  {- ^ Collected function symbols consisting of
  * name :: Text
  * arity :: Int
  * first occurence :: Pos
  -}
  , _predicateSymbols :: Map Text (Int, Pos)
  {- ^ Collected predicate symbols consisting of
  * name :: Text
  * arity :: Int
  * first occurence :: Pos
  -}
  , _rules :: Map Name RuleSpec
  -- ^ A map that contains all rules, mapping their names to their specification
  }
  deriving (Show, Eq)

-- * Initial constructors
initialModel ::
  -- | The starting proof
  Proof ->
  -- | A list of operators (alias, operator, arity)
  [(Text, Text, Int)] ->
  -- | A list of quantifiers (alias, quantifier)
  [(Text, Text)] ->
  -- | A list of infix predicates (alias, predicate name)
  [(Text, Text)] ->
  -- | The map of rules
  Map Name RuleSpec ->
  Model
initialModel p operators infixPreds quantifiers rules =
  Model
    { _focusedLine = Nothing
    , _proof = p
    , _dragTarget = Nothing
    , _spawnType = Nothing
    , _currentHoverLine = Nothing
    , _dragging = False
    , _operators = operators
    , _infixPreds = infixPreds
    , _quantifiers = quantifiers
    , _functionSymbols = mempty
    , _predicateSymbols = mempty
    , _rules = rules
    }

-- * Lenses
focusedLine :: Lens Model (Maybe (Either NodeAddr NodeAddr))
focusedLine = lens (._focusedLine) $ \model a -> model{_focusedLine = a}

proof :: Lens Model Proof
proof = lens (._proof) $ \model p -> model{_proof = p}

dragTarget :: Lens Model (Maybe (Either NodeAddr ProofAddr))
dragTarget = lens (._dragTarget) $ \model dt -> model{_dragTarget = dt}

spawnType :: Lens Model (Maybe SpawnType)
spawnType = lens (._spawnType) $ \model st -> model{_spawnType = st}

currentHoverLine :: Lens Model (Maybe NodeAddr)
currentHoverLine = lens (._currentHoverLine) $ \model dt -> model{_currentHoverLine = dt}

dragging :: Lens Model Bool
dragging = lens (._dragging) $ \model d -> model{_dragging = d}

operators :: Lens Model [(Text, Text, Int)]
operators = lens (._operators) $ \model op -> model{_operators = op}

infixPreds :: Lens Model [(Text, Text)]
infixPreds = lens (._infixPreds) $ \model p -> model{_infixPreds = p}

quantifiers :: Lens Model [(Text, Text)]
quantifiers = lens (._quantifiers) $ \model q -> model{_quantifiers = q}

functionSymbols :: Lens Model (Map Text (Int, Pos))
functionSymbols = lens (._functionSymbols) $ \model fs -> model{_functionSymbols = fs}

predicateSymbols :: Lens Model (Map Text (Int, Pos))
predicateSymbols = lens (._predicateSymbols) $ \model ps -> model{_predicateSymbols = ps}

rules :: Lens Model (Map Name RuleSpec)
rules = lens (._rules) $ \model rs -> model{_rules = rs}

-- * Semantic checking

checkFreshness :: forall m. (MonadState Model m) => m ()
checkFreshness = do
  proof <~ (use proof >>= \p -> pure (pMapLinesWithAddr (under . goFormula p) (const id) p))
 where
  goFormula :: Proof -> NodeAddr -> Formula -> Formula
  goFormula _ _ a@(Unparsed{}; ParsedInvalid{}) = a
  goFormula p na a@(ParsedValid txt f@(FreshVar v)) = case pCollectFreshnessNodes na p of
    Left err -> ParsedInvalid (getText a) err f
    Right nodes ->
      case isFreshList v nodes of
        Nothing -> a
        Just (naf', f') ->
          ParsedInvalid
            (getText a)
            ( "Could not verify freshness of "
                <> v
                <> "\nIt appears in formula:\n"
                <> show (lineNoOr999 naf' p)
                <> "|"
                <> prettyPrint f'
            )
            f
  goFormula _ _ a@(fromWrapper -> Just _) = a
  isFreshList :: Name -> [(NodeAddr, Either Assumption Derivation)] -> Maybe (NodeAddr, RawFormula)
  isFreshList v [] = Nothing
  isFreshList v ((na, Left (fromWrapper -> Nothing)) : rest) = isFreshList v rest
  isFreshList v ((na, Left (fromWrapper -> Just f)) : rest) = if isFresh v f then isFreshList v rest else Just (na, un f)
  isFreshList v ((na, Right (Derivation f _)) : rest) = isFreshList v ((na, Left (un f)) : rest)

{- | Recalculates the list of functionsymbols and predicatesymbols in the model.

This is done by iterating over the proof and collecting all symbols.
The first occurence of a symbol fixes its arity, and all following symbols with the same name are compared to this arity.
-}
regenerateSymbols :: forall m. (MonadState Model m) => m ()
regenerateSymbols = do
  functionSymbols .= mempty
  predicateSymbols .= mempty
  proof <~ (use proof >>= pMapLinesMAccumL goAssumption goLine 1 <&> snd)
 where
  goAssumption :: Int -> Assumption -> m (Int, Assumption)
  goAssumption n a@(Unparsed{}) = pure (n + 1, a)
  goAssumption n a@(ParsedInvalid txt err (RawAssumption f)) = second (RawAssumption <$>) <$> goFormula n (ParsedInvalid txt err f)
  goAssumption n a@(ParsedValid txt (RawAssumption f)) = second (RawAssumption <$>) <$> goFormula n (ParsedValid txt f)
  -- collect symbols inside a formula
  goFormula :: Int -> Formula -> m (Int, Formula)
  -- skip unparsed formulae
  goFormula n a@(Unparsed{}) = pure (n + 1, a)
  goFormula n a =
    let (formula, txt) = case a of
          (ParsedInvalid txt _ f) -> (f, txt)
          (ParsedValid txt f) -> (f, txt)
     in do
          -- fetch current lists of symbols
          fsyms <- use functionSymbols
          psyms <- use predicateSymbols
          a' <- go n fsyms psyms txt formula
          pure (n + 1, a')
   where
    goArgs :: Int -> Map Text (Int, Pos) -> [Term] -> m (Maybe Text)
    goArgs n fsyms = foldlM (\mErr t -> if isJust mErr then pure mErr else goTerm n fsyms t) Nothing
     where
      goTerm :: Int -> Map Text (Int, Pos) -> Term -> m (Maybe Text)
      goTerm _ _ (Var{}) = pure Nothing
      goTerm n fsyms (Fun name args) = do
        -- first check inner symbols
        mTermError <- goArgs n fsyms args
        case mTermError of
          Just termError -> pure $ Just termError
          Nothing ->
            -- then check the function symbol
            case fsyms !? name of
              Nothing -> do
                functionSymbols %= insert name (length args, n)
                pure Nothing
              Just (expLen, pos) ->
                pure $
                  if expLen == length args
                    then Nothing
                    else
                      Just $
                        "Function symbol "
                          <> show name
                          <> " has "
                          <> show (length args)
                          <> " arguments,\nbut in line "
                          <> show pos
                          <> " it appears with "
                          <> show expLen
                          <> " arguments."
    -- proccesses a single formula.
    go :: Int -> Map Text (Int, Pos) -> Map Text (Int, Pos) -> Text -> RawFormula -> m Formula
    go n fsyms psyms txt formula@(Pred name args) = do
      -- first check function symbols
      mTermError <- goArgs n fsyms args
      case mTermError of
        Just termError -> pure $ ParsedInvalid txt termError formula
        -- then check the predicate symbol
        Nothing ->
          case psyms !? name of
            Nothing -> do
              predicateSymbols %= insert name (length args, n)
              pure (ParsedValid txt formula)
            Just (expLen, pos) ->
              pure $
                if expLen == length args
                  then ParsedValid txt formula
                  -- TODO singular/plural!
                  else
                    ParsedInvalid
                      txt
                      ( "Predicate symbol "
                          <> name
                          <> " has "
                          <> show (length args)
                          <> " arguments,\nbut in line "
                          <> show pos
                          <> " it appears with "
                          <> show expLen
                          <> " arguments."
                      )
                      formula
    go n fsyms psyms txt form@(Opr name fs) = foldlM (\r f -> go n fsyms psyms txt f <&> combineWrappers r) (ParsedValid txt form) fs
     where
      combineWrappers :: Wrapper RawFormula -> Wrapper RawFormula -> Wrapper RawFormula
      combineWrappers (Unparsed _ err) _ = Unparsed txt err
      combineWrappers (ParsedInvalid{}) (Unparsed _ err) = Unparsed txt err
      combineWrappers (ParsedInvalid _ err _) (ParsedInvalid{}) = ParsedInvalid txt err form
      combineWrappers (ParsedInvalid _ err _) (ParsedValid{}) = ParsedInvalid txt err form
      combineWrappers (ParsedValid{}) (Unparsed _ err) = Unparsed txt err
      combineWrappers (ParsedValid{}) (ParsedInvalid _ err _) = ParsedInvalid txt err form
      combineWrappers (ParsedValid{}) (ParsedValid{}) = ParsedValid txt form
    go n fsyms psyms txt (Quantifier name variable formula) = go n fsyms psyms txt formula <&> (Quantifier name variable <$>)
    go _ _ _ txt (FreshVar var) = pure $ ParsedValid txt $ FreshVar var
  -- proccesses a single line, by proccessing its formula.
  goLine :: Int -> Derivation -> m (Int, Derivation)
  goLine n (Derivation f r) = do
    (n', f') <- goFormula n f
    pure (n', Derivation f' r)