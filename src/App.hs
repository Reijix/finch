module App (runApp) where

import App.Syntax
import App.Views
import Control.Monad (when)
import qualified Data.Map as M
import Miso
  ( App,
    CSS (Href),
    Component (events, styles, subs),
    Effect,
    PointerEvent (client),
    ROOT,
    View,
    component,
    consoleLog,
    defaultEvents,
    defaultOptions,
    dragEvents,
    emptyDecoder,
    focus,
    io_,
    mouseSub,
    ms,
    preventDefault,
    run,
    startApp,
    text,
  )
import qualified Miso.CSS as CSS
import qualified Miso.CSS as HP
import Miso.CSS.Color (red)
import Miso.Effect (Sub)
import qualified Miso.Html.Element as H
import Miso.Html.Event
import qualified Miso.Html.Property as HP
import Miso.Lens (use, (%=), (.=))
import Miso.Svg (text_)
import Proof.Syntax

-----------------------------------------------------------------------------

-- | Test of Haddock
runApp ::
  forall formula rule.
  (Eq formula) =>
  (Show formula) =>
  (Eq rule) =>
  (Show rule) =>
  Model rule formula ->
  IO ()
runApp emptyModel = run $ startApp app
  where
    app :: App (Model rule formula) Action
    app =
      (component emptyModel updateModel viewModel)
        { styles = [Href "style.css"],
          events = M.union dragEvents (M.fromList [("dblclick", False), ("focusout", False)])
        }

-----------------------------------------------------------------------------
updateModel :: Action -> Effect ROOT (Model rule formula) Action
updateModel (Drop LocationBin) = do
  dt <- use dragTarget
  case dt of
    TargetProof n -> pure ()
    TargetLine n -> proof %= lRemove n
    TargetNone -> pure ()
  io_ . consoleLog $ "dropped in bin"
updateModel (Drop (LocationLine n)) = do
  io_ . consoleLog . ms $ "dropped in line " ++ show n
updateModel (Drop (LocationProof _)) = pure ()
updateModel DragEnter = pure ()
updateModel DragLeave = pure ()
updateModel (DragStart dt) = do
  dragTarget .= dt
  case dt of
    TargetNone -> io_ . consoleLog $ "dragstartNone"
    TargetLine n -> io_ . consoleLog . ms $ "dragstartLine" ++ show n
    TargetProof n -> io_ . consoleLog . ms $ "dragstartProof" ++ show n
updateModel DragOver = pure ()
updateModel DragEnd = io_ . consoleLog $ "dragend"
updateModel (DoubleClick n) = do
  focusedLine .= n
  io_ . focus . ms $ "proof-line" ++ show n
-- io_ . select . ms $ "proof-line" ++ show n
updateModel Blur = do
  io_ . consoleLog $ "blur"
  focusedLine .= -1

-----------------------------------------------------------------------------
viewModel ::
  forall formula rule.
  (Show formula) =>
  (Show rule) =>
  Model rule formula ->
  View (Model rule formula) Action
viewModel model =
  H.div_
    []
    [ viewProof model,
      viewBin
    ]

-----------------------------------------------------------------------------