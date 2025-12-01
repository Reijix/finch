module App.Model where

import Data.List qualified as L
import Data.Text (Text)
import Fitch.Proof
import Miso
  ( App,
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
  ProcessInput :: MisoString -> Int -> Int -> NodeAddr -> Action
  DoubleClick :: NodeAddr -> Action
  Drop :: DropLocation -> Action
  DragEnter :: NodeAddr -> InsertPosition -> Action
  DragLeave :: InsertPosition -> Action
  DragOver :: Action
  DragStart :: NodeAddr -> Action
  SpawnStart :: SpawnType -> Action
  DragEnd :: Action
  Drag :: Action
  Nop :: Action
  ProcessParens :: NodeAddr -> Int -> Int -> Action
  KeyDownStart :: DOMRef -> Action
  KeyDownStop :: Action

-----------------------------------------------------------------------------

initialModel :: Proof -> [(Text, Text)] -> [(Text, Text)] -> Model
initialModel p unaryOperators binaryOperators =
  Model
    { _focusedLine = Nothing,
      _proof = p,
      _dragTarget = Nothing,
      _spawnType = Nothing,
      _currentLineBefore = Nothing,
      _currentLineAfter = Nothing,
      _dragging = False,
      _functionSymbols = [],
      _predicateSymbols = [],
      _unaryOperators = unaryOperators,
      _binaryOperators = binaryOperators,
      _quantifiers = [],
      _firstOrder = False
    }

initialModelFirstOrder :: Proof -> [(Text, Int)] -> [(Text, Int)] -> [(Text, Text)] -> [(Text, Text)] -> [(Text, Text)] -> Model
initialModelFirstOrder p functionSymbols predicateSymbols unaryOperators binaryOperators quantifiers =
  Model
    { _focusedLine = Nothing,
      _proof = p,
      _dragTarget = Nothing,
      _spawnType = Nothing,
      _currentLineBefore = Nothing,
      _currentLineAfter = Nothing,
      _dragging = False,
      _functionSymbols = functionSymbols,
      _predicateSymbols = predicateSymbols,
      _unaryOperators = unaryOperators,
      _binaryOperators = binaryOperators,
      _quantifiers = quantifiers,
      _firstOrder = True
    }

data Model = Model
  { _focusedLine :: Maybe NodeAddr,
    _proof :: Proof,
    _dragTarget :: Maybe NodeAddr,
    _spawnType :: Maybe SpawnType,
    _currentLineBefore :: Maybe NodeAddr,
    _currentLineAfter :: Maybe NodeAddr,
    _dragging :: Bool,
    _functionSymbols :: [(Text, Int)],
    _predicateSymbols :: [(Text, Int)],
    _unaryOperators :: [(Text, Text)],
    _binaryOperators :: [(Text, Text)],
    _quantifiers :: [(Text, Text)],
    _firstOrder :: Bool
  }
  deriving (Show, Eq)

focusedLine :: Lens Model (Maybe NodeAddr)
focusedLine = lens (._focusedLine) $ \model a -> model {_focusedLine = a}

proof :: Lens Model Proof
proof = lens (._proof) $ \model p -> model {_proof = p}

dragTarget :: Lens Model (Maybe NodeAddr)
dragTarget = lens (._dragTarget) $ \model dt -> model {_dragTarget = dt}

spawnType :: Lens Model (Maybe SpawnType)
spawnType = lens (._spawnType) $ \model st -> model {_spawnType = st}

currentLineBefore :: Lens Model (Maybe NodeAddr)
currentLineBefore = lens (._currentLineBefore) $ \model dt -> model {_currentLineBefore = dt}

currentLineAfter :: Lens Model (Maybe NodeAddr)
currentLineAfter = lens (._currentLineAfter) $ \model dt -> model {_currentLineAfter = dt}

dragging :: Lens Model Bool
dragging = lens (._dragging) $ \model d -> model {_dragging = d}

functionSymbols :: Lens Model [(Text, Int)]
functionSymbols = lens (._functionSymbols) $ \model fs -> model {_functionSymbols = fs}

predicateSymbols :: Lens Model [(Text, Int)]
predicateSymbols = lens (._predicateSymbols) $ \model ps -> model {_predicateSymbols = ps}

unaryOperators :: Lens Model [(Text, Text)]
unaryOperators = lens (._unaryOperators) $ \model uo -> model {_unaryOperators = uo}

binaryOperators :: Lens Model [(Text, Text)]
binaryOperators = lens (._binaryOperators) $ \model bo -> model {_binaryOperators = bo}

quantifiers :: Lens Model [(Text, Text)]
quantifiers = lens (._quantifiers) $ \model q -> model {_quantifiers = q}

firstOrder :: Lens Model Bool
firstOrder = lens (._firstOrder) $ \model fo -> model {_firstOrder = fo}
