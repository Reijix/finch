module App (runApp) where

import App.Syntax
import App.Views
import Control.Monad (when)
import Data.Map qualified as M
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
    fromMisoString,
    io_,
    keyboardEvents,
    mouseSub,
    ms,
    preventDefault,
    run,
    startApp,
    text,
  )
import Miso.CSS qualified as CSS
import Miso.CSS qualified as HP
import Miso.CSS.Color (red)
import Miso.Effect (Sub)
import Miso.Html.Element qualified as H
import Miso.Html.Event
import Miso.Html.Property qualified as HP
import Miso.Lens (use, (%=), (.=), (^.))
import Miso.Svg (text_)
import Proof.Syntax

-----------------------------------------------------------------------------

-- | Test of Haddock
runApp ::
  forall formula rule.
  (Eq formula) =>
  (Show formula) =>
  (FromString formula) =>
  (Eq rule) =>
  (Show rule) =>
  Model formula rule ->
  IO ()
runApp emptyModel = run $ startApp app
  where
    app :: App (Model formula rule) Action
    app =
      (component emptyModel updateModel viewModel)
        { styles = [Href "style.css"],
          events = dragEvents <> M.fromList [("dblclick", False), ("focusout", False)] <> keyboardEvents <> defaultEvents
        }

-----------------------------------------------------------------------------
updateModel :: forall formula rule. (FromString formula) => Action -> Effect ROOT (Model formula rule) Action
updateModel (Drop LocationBin) = do
  dt <- use dragTarget
  case dt of
    Nothing -> pure ()
    Just addr -> proof %= lRemove addr
  io_ . consoleLog $ "dropped in bin"
updateModel (Drop (LocationAddr targetAddr pos)) = do
  use dragTarget >>= \case
    Nothing -> pure ()
    Just sourceAddr -> do
      io_ . consoleLog . ms $ "dropping (" ++ show sourceAddr ++ ") into (" ++ show targetAddr ++ ")"
      proof %= lMove targetAddr pos sourceAddr
  use spawnType >>= \case
    Nothing -> pure ()
    Just SpawnLine -> undefined
    Just SpawnProof -> undefined
    Just SpawnAssumption -> undefined
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
-- updateModel DragOver = pure ()
updateModel DragEnd = do
  currentLineAfter .= Nothing
  currentLineBefore .= Nothing
  dragging .= False
  dragTarget .= Nothing
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
updateModel (Input str) = do
  io_ . consoleLog $ "input"
  fline <- use focusedLine
  case fline of
    Nothing -> pure ()
    Just addr -> do
      io_ . consoleLog . ms $ "printing " ++ show str
      case fromString (fromMisoString str :: String) of
        Left f -> proof %= lUpdateFormula f addr
        Right _ -> undefined -- TODO

-----------------------------------------------------------------------------
-- TODO: Add Buttons for adding Nodes as next step.
viewModel ::
  forall formula rule.
  (Show formula) =>
  (Show rule) =>
  Model formula rule ->
  View (Model formula rule) Action
viewModel model =
  H.div_
    []
    [ viewProof model,
      viewBin,
      viewInsertLineNode
      -- H.p_ [] [text $ ms $ show (model ^. proof)]
    ]

-----------------------------------------------------------------------------