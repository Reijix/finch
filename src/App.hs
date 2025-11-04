module App (runApp) where

import App.Syntax
import App.Views
import Control.Monad (when)
import qualified Data.Map as M
import Data.Maybe (fromJust, fromMaybe)
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
    Nothing -> pure ()
    Just addr -> proof %= lRemove addr
  io_ . consoleLog $ "dropped in bin"
updateModel (Drop (LocationAddr n)) = do
  io_ . consoleLog . ms $ "dropped in addr " ++ show n
updateModel (DragEnter a Before) = do
  -- io_ . consoleLog . ms $ "dragenter " ++ show a
  currentLineBefore .= Just a
updateModel (DragEnter a After) = do
  -- io_ . consoleLog . ms $ "dragenter " ++ show a
  currentLineAfter .= Just a
updateModel (DragLeave Before) = do
  -- io_ . consoleLog . ms $ "dragleave"
  currentLineBefore .= Nothing
updateModel (DragLeave After) = do
  -- io_ . consoleLog . ms $ "dragleave"
  currentLineAfter .= Nothing
updateModel (DragStart dt) = do
  dragTarget .= Just dt
  dragging .= True
  io_ . consoleLog . ms $ "dragstart " ++ show dt
updateModel DragOver = pure ()
updateModel DragEnd = do
  dragging .= False
  io_ . consoleLog $ "dragend"
updateModel (DoubleClick a) = do
  focusedLine .= Just a
  p <- use proof
  io_ . focus . ms $ "proof-line" ++ show (fromJust (fromNodeAddr a p))
-- io_ . select . ms $ "proof-line" ++ show n
updateModel Blur = do
  io_ . consoleLog $ "blur"
  focusedLine .= Nothing
updateModel Nop = pure ()
updateModel (SpawnStart _) =
  io_ . consoleLog $ "spawnstart"

-----------------------------------------------------------------------------
-- TODO: Add Buttons for adding Nodes as next step.
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
      viewBin,
      viewInsertLineNode
    ]

-----------------------------------------------------------------------------