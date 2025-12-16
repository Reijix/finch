module App.Model where

import Control.Monad (foldM)
import Control.Monad.RWS (MonadState)
import Data.List qualified as L
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe (isJust)
import Data.Text (Text, pack)
import Fitch.Proof
import Miso (
  App,
  Attribute,
  Component (events, subs),
  DOMRef,
  Effect,
  KeyCode,
  KeyInfo,
  MisoString,
  PointerEvent (client),
  ROOT,
  View,
  component,
  consoleLog,
  io_,
  mouseSub,
  ms,
  onWithOptions,
  pointerDecoder,
  preventDefault,
  run,
  startApp,
  text,
 )
import Miso.CSS qualified as CSS
import Miso.Lens
import Miso.Svg.Element qualified as S
import Miso.Svg.Property qualified as SP

-----------------------------------------------------------------------------

-- * Types

data DropLocation where
  LocationAddr :: NodeAddr -> InsertPosition -> DropLocation
  LocationBin :: DropLocation
  deriving (Show, Eq)

data SpawnType where
  SpawnLine :: SpawnType
  SpawnProof :: SpawnType
  SpawnAssumption :: SpawnType
  deriving (Show, Eq)

data Action where
  Blur :: Action
  Input :: MisoString -> DOMRef -> Action
  Change :: Action
  ProcessInput :: MisoString -> Int -> Int -> Either NodeAddr NodeAddr -> Action
  DoubleClick :: Either NodeAddr NodeAddr -> Action
  Drop :: DropLocation -> Action
  DragEnter :: NodeAddr -> InsertPosition -> Action
  DragLeave :: InsertPosition -> Action
  DragOver :: Action
  DragStart :: NodeAddr -> Action
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
  , _dragTarget :: Maybe NodeAddr
  -- ^ the element that is currently being dragged
  , _spawnType :: Maybe SpawnType
  -- ^ the type of element that is currently being spawned
  , _currentLineBefore :: Maybe NodeAddr
  -- ^ the line before which the user currently hovers
  , _currentLineAfter :: Maybe NodeAddr
  -- ^ the line after which the user currently hovers
  , _dragging :: Bool
  -- ^ denotes whether the user is currently dragging an element
  , _unaryOperators :: [(Text, Text)]
  {- ^ list of unary operators, consisting of (alias, symbol)
  where alias is an alternative notation for the symbol
  -}
  , _binaryOperators :: [(Text, Text)]
  {- ^ list of binary operators, consisting of (alias, symbol)
  where alias is an alternative notation for the symbol
  -}
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
  }
  deriving (Show, Eq)

-- * Initial constructors
initialModel :: Proof -> [(Text, Text)] -> [(Text, Text)] -> [(Text, Text)] -> Model
initialModel p unaryOperators binaryOperators quantifiers =
  Model
    { _focusedLine = Nothing
    , _proof = p
    , _dragTarget = Nothing
    , _spawnType = Nothing
    , _currentLineBefore = Nothing
    , _currentLineAfter = Nothing
    , _dragging = False
    , _unaryOperators = unaryOperators
    , _binaryOperators = binaryOperators
    , _quantifiers = quantifiers
    , _functionSymbols = M.empty
    , _predicateSymbols = M.empty
    }

-- * Lenses
focusedLine :: Lens Model (Maybe (Either NodeAddr NodeAddr))
focusedLine = lens (._focusedLine) $ \model a -> model{_focusedLine = a}

proof :: Lens Model Proof
proof = lens (._proof) $ \model p -> model{_proof = p}

dragTarget :: Lens Model (Maybe NodeAddr)
dragTarget = lens (._dragTarget) $ \model dt -> model{_dragTarget = dt}

spawnType :: Lens Model (Maybe SpawnType)
spawnType = lens (._spawnType) $ \model st -> model{_spawnType = st}

currentLineBefore :: Lens Model (Maybe NodeAddr)
currentLineBefore = lens (._currentLineBefore) $ \model dt -> model{_currentLineBefore = dt}

currentLineAfter :: Lens Model (Maybe NodeAddr)
currentLineAfter = lens (._currentLineAfter) $ \model dt -> model{_currentLineAfter = dt}

dragging :: Lens Model Bool
dragging = lens (._dragging) $ \model d -> model{_dragging = d}

unaryOperators :: Lens Model [(Text, Text)]
unaryOperators = lens (._unaryOperators) $ \model uo -> model{_unaryOperators = uo}

binaryOperators :: Lens Model [(Text, Text)]
binaryOperators = lens (._binaryOperators) $ \model bo -> model{_binaryOperators = bo}

quantifiers :: Lens Model [(Text, Text)]
quantifiers = lens (._quantifiers) $ \model q -> model{_quantifiers = q}

functionSymbols :: Lens Model (Map Text (Int, Pos))
functionSymbols = lens (._functionSymbols) $ \model fs -> model{_functionSymbols = fs}

predicateSymbols :: Lens Model (Map Text (Int, Pos))
predicateSymbols = lens (._predicateSymbols) $ \model ps -> model{_predicateSymbols = ps}

-- * Semantic checking

{- | Recalculates the list of functionsymbols and predicatesymbols in the model.

This is done by iterating over the proof and collecting all symbols.
The first occurence of a symbol fixes its arity, and all following symbols with the same name are compared to this arity.
-}
regenerateSymbols :: forall m. (MonadState Model m) => m ()
regenerateSymbols = do
  functionSymbols .= M.empty
  predicateSymbols .= M.empty
  proof <~ (use proof >>= pMapMAccumL goFormula goLine 1 <&> snd)
 where
  -- collect symbols inside a formula
  goFormula :: Int -> Assumption -> m (Int, Assumption)
  -- skip unparsed formulae
  goFormula n a@(Unparsed{}) = pure (n + 1, a)
  goFormula n a =
    let (formula, txt) = (fromWrapper a, getText a)
     in do
          -- fetch current lists of symbols
          fsyms <- use functionSymbols
          psyms <- use predicateSymbols
          a' <- go n fsyms psyms txt formula
          return (n + 1, a')
   where
    goArgs :: Int -> Map Text (Int, Pos) -> [Term] -> m (Maybe Text)
    goArgs n fsyms = foldM (\mErr t -> if isJust mErr then return mErr else goTerm n fsyms t) Nothing
     where
      goTerm :: Int -> Map Text (Int, Pos) -> Term -> m (Maybe Text)
      goTerm _ _ (Var{}) = return Nothing
      goTerm n fsyms (Fun name args) = do
        -- first check inner symbols
        mTermError <- goArgs n fsyms args
        case mTermError of
          Just termError -> return $ Just termError
          Nothing ->
            -- then check the function symbol
            case fsyms M.!? name of
              Nothing -> do
                functionSymbols %= M.insert name (length args, n)
                return Nothing
              Just (expLen, pos) ->
                return $
                  if expLen == length args
                    then Nothing
                    else Just . pack $ "Function symbol " ++ show name ++ " has " ++ show (length args) ++ " arguments,\nbut in line " ++ show pos ++ " it appears with " ++ show expLen ++ " arguments."
    -- proccesses a single formula.
    go :: Int -> Map Text (Int, Pos) -> Map Text (Int, Pos) -> Text -> Formula -> m Assumption
    go n fsyms psyms txt formula@(Predicate name args) = do
      -- first check function symbols
      mTermError <- goArgs n fsyms args
      case mTermError of
        Just termError -> return $ ParsedInvalid txt termError formula
        -- then check the predicate symbol
        Nothing ->
          case psyms M.!? name of
            Nothing -> do
              predicateSymbols %= M.insert name (length args, n)
              return (ParsedValid txt formula)
            Just (expLen, pos) ->
              return $
                if expLen == length args
                  then ParsedValid txt formula
                  -- TODO singular/plural!
                  else ParsedInvalid txt (pack $ "Predicate symbol " ++ show name ++ " has " ++ show (length args) ++ " arguments,\nbut in line " ++ show pos ++ " it appears with " ++ show expLen ++ " arguments.") formula
    go n fsyms psyms txt (UnaryOp name formula) = go n fsyms psyms txt formula <&> (UnaryOp name <$>)
    go n fsyms psyms txt f@(BinaryOp name formula1 formula2) = do
      f1 <- go n fsyms psyms txt formula1
      f2 <- go n fsyms psyms txt formula2
      case f1 of
        -- (Unparsed _ err) -> return (Unparsed txt err)
        (ParsedInvalid _ err _) -> return (ParsedInvalid txt err f)
        (ParsedValid _ _) -> case f2 of
          -- (Unparsed _ err) -> return (Unparsed txt err)
          (ParsedInvalid _ err _) -> return (ParsedInvalid txt err f)
          (ParsedValid _ _) -> return (ParsedValid txt f)
    go n fsyms psyms txt (Quantifier name variable formula) = go n fsyms psyms txt formula <&> (Quantifier name variable <$>)
  -- proccesses a single line, by proccessing its formula.
  goLine :: Int -> Derivation -> m (Int, Derivation)
  goLine n (Derivation f r) = do
    (n', f') <- goFormula n f
    return (n', Derivation f' r)