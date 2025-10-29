module App.Syntax where

import qualified Data.List as L
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
import qualified Miso.CSS as CSS
import Miso.Lens (Lens, lens, this, use, (.=), (^.))
import Miso.Svg (text_, tspan_)
import qualified Miso.Svg.Element as S
import qualified Miso.Svg.Property as SP
import Proof.Syntax

-----------------------------------------------------------------------------
data DropLocation where
  LocationAddr :: NodeAddr -> DropLocation
  LocationBin :: DropLocation
  deriving (Show, Eq)

-- data DragTarget where
--   TargetProof :: Int -> DragTarget
--   TargetLine :: Int -> DragTarget
--   TargetNone :: DragTarget
--   deriving (Show, Eq)

data Action where
  Blur :: Action
  DoubleClick :: NodeAddr -> Action
  Drop :: DropLocation -> Action
  DragEnter :: Action
  DragLeave :: Action
  DragOver :: Action
  DragStart :: NodeAddr -> Action
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
    _dragTarget :: Maybe NodeAddr
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