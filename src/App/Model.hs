module App.Model where

import Data.List qualified as L
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text (Text)
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
import Miso.Lens (Lens, lens, use, (.=), (^.))
import Miso.Svg.Element qualified as S
import Miso.Svg.Property qualified as SP

-----------------------------------------------------------------------------
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

newtype Pos = Pos (Int, Int) deriving (Show, Eq)

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