module App.Syntax where

import Data.List qualified as L
import Miso
  ( App,
    Attribute,
    Component (events, subs),
    Effect,
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
import Miso.Lens (Lens, lens, this, use, (.=), (^.))
import Miso.Svg (text_, tspan_)
import Miso.Svg.Element qualified as S
import Miso.Svg.Property qualified as SP
import Proof.Syntax

-----------------------------------------------------------------------------
class FromString a where
  fromString :: String -> Either a String

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
  Input :: MisoString -> Action
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
  deriving (Show, Eq)

-----------------------------------------------------------------------------
-- actually, just keep track of current element, this can be an either (proof, line or formula) and then insert a phantom object into the proof tree.

data Model formula rule = Model
  { _cursorX :: Double,
    _cursorY :: Double,
    _focusedLine :: Maybe NodeAddr,
    _proof :: Proof formula rule,
    _dragTarget :: Maybe NodeAddr,
    _spawnType :: Maybe SpawnType,
    _currentLineBefore :: Maybe NodeAddr,
    _currentLineAfter :: Maybe NodeAddr,
    _dragging :: Bool
  }
  deriving (Show, Eq)

focusedLine :: Lens (Model formula rule) (Maybe NodeAddr)
focusedLine = lens (._focusedLine) $ \model a -> model {_focusedLine = a}

cursorX :: Lens (Model formula rule) Double
cursorX = lens (._cursorX) $ \model x -> model {_cursorX = x}

cursorY :: Lens (Model formula rule) Double
cursorY = lens (._cursorY) $ \model y -> model {_cursorY = y}

proof :: Lens (Model formula rule) (Proof formula rule)
proof = lens (._proof) $ \model p -> model {_proof = p}

dragTarget :: Lens (Model formula rule) (Maybe NodeAddr)
dragTarget = lens (._dragTarget) $ \model dt -> model {_dragTarget = dt}

spawnType :: Lens (Model formula rule) (Maybe SpawnType)
spawnType = lens (._spawnType) $ \model st -> model {_spawnType = st}

currentLineBefore :: Lens (Model formula rule) (Maybe NodeAddr)
currentLineBefore = lens (._currentLineBefore) $ \model dt -> model {_currentLineBefore = dt}

currentLineAfter :: Lens (Model formula rule) (Maybe NodeAddr)
currentLineAfter = lens (._currentLineAfter) $ \model dt -> model {_currentLineAfter = dt}

dragging :: Lens (Model formula rule) Bool
dragging = lens (._dragging) $ \model x -> model {_dragging = x}