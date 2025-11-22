module App.Runner (runApp, Proof (..), FromString (..), Model (..), Derivation (..)) where

import App.Model
import App.Views
import Control.Monad.State
import Data.Map qualified as M
import Data.Maybe (fromJust, fromMaybe)
import Fitch.Proof
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
import Miso.Lens (Lens, use, (%=), (.=), (^.))
import Miso.Svg (text_)

(%=?) :: (MonadState record m) => Lens record field -> (field -> Maybe field) -> m ()
(%=?) _lens f = _lens %= (\x -> fromMaybe x (f x))

-----------------------------------------------------------------------------

-- | Test of Haddock
runApp ::
  forall formula rule.
  (Eq formula) =>
  (Show formula) =>
  (FromString formula) =>
  (Eq rule) =>
  (Show rule) =>
  (FromString rule) =>
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
updateModel ::
  forall formula rule.
  (FromString formula) =>
  (FromString rule) =>
  Action -> Effect ROOT (Model formula rule) Action
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
    Just SpawnLine -> proof %=? lInsert (Right . ProofLine $ Derivation (tryParse "Formula") (tryParse "Rule")) targetAddr pos
    Just SpawnProof -> proof %=? lInsert (Right $ SubProof [] [] (Derivation (tryParse "Formula") (tryParse "Rule"))) targetAddr pos
    Just SpawnAssumption -> proof %=? lInsert (Left (tryParse "Formula")) targetAddr pos
updateModel (DragEnter a Before) = currentLineBefore .= Just a
updateModel (DragEnter a After) = currentLineAfter .= Just a
-- NOTE: the check for `Before` and `After` is actually needed, because processing order of events is not guaranteed.
updateModel (DragLeave Before) = currentLineBefore .= Nothing
updateModel (DragLeave After) = currentLineAfter .= Nothing
updateModel (DragStart dt) = do
  dragTarget .= Just dt
  dragging .= True
updateModel DragEnd = do
  currentLineAfter .= Nothing
  currentLineBefore .= Nothing
  dragging .= False
  dragTarget .= Nothing
  spawnType .= Nothing
updateModel (DoubleClick a) = do
  focusedLine .= Just a
  p <- use proof
  io_ . focus . ms $ "proof-line" ++ show (fromJust (fromNodeAddr a p))
-- TODO implement select upstream
-- io_ . select . ms $ "proof-line" ++ show n
updateModel Blur = do
  focusedLine .= Nothing
updateModel Nop = pure ()
updateModel (SpawnStart st) = spawnType .= Just st
-- TODO: Maybe actual parse should only happen on enter, i.e. when `blur` fires.
updateModel (Input str) = do
  fline <- use focusedLine
  mapM_ (\addr -> proof %= lUpdateFormula (tryParse (fromMisoString str :: String)) addr) fline

-----------------------------------------------------------------------------
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
      viewSpawnNode SpawnLine "Insert Line",
      viewSpawnNode SpawnAssumption "Insert Assumption",
      viewSpawnNode SpawnProof "Insert Proof"
    ]

-----------------------------------------------------------------------------