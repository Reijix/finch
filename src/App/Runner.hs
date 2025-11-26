module App.Runner (runApp, initialModel, tryParse, runAppFirstOrder, Proof (..), FromText (..), Model (..), Derivation (..)) where

import App.Model
import App.Views
import Control.Monad.State
import Data.Map qualified as M
import Data.Maybe (fromJust, fromMaybe)
import Data.Text (Text, replace)
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
import Parser.Formula

(%=?) :: (MonadState record m) => Lens record field -> (field -> Maybe field) -> m ()
(%=?) _lens f = _lens %= (\x -> fromMaybe x (f x))

-----------------------------------------------------------------------------

-- | Test of Haddock
runApp :: Proof -> [(Text, Text)] -> [(Text, Text)] -> IO ()
runApp p unaryOperators binaryOperators =
  run . startApp $
    (component m updateModel viewModel)
      { styles = [Href "style.css"],
        events = dragEvents <> M.fromList [("dblclick", False), ("focusout", False)] <> keyboardEvents <> defaultEvents
      }
  where
    m = initialModel p unaryOperators binaryOperators

runAppFirstOrder :: Proof -> [(Text, Int)] -> [(Text, Int)] -> [(Text, Text)] -> [(Text, Text)] -> [(Text, Text)] -> IO ()
runAppFirstOrder p functionSymbols predicateSymbols unaryOperators binaryOperators quantifiers =
  run . startApp $
    (component m updateModel viewModelFirstOrder)
      { styles = [Href "style.css"],
        events = dragEvents <> M.fromList [("dblclick", False), ("focusout", False)] <> keyboardEvents <> defaultEvents
      }
  where
    m = initialModelFirstOrder p functionSymbols predicateSymbols unaryOperators binaryOperators quantifiers

-----------------------------------------------------------------------------
class FromText a where
  fromText :: Model -> Text -> Either Text a

instance FromText Rule where
  fromText :: Model -> Text -> Either Text Rule
  fromText m str = Right $ Rule str [] (Predicate "" [])

instance FromText Formula where
  fromText :: Model -> Text -> Either Text Formula
  fromText m = parseFormula (m ^. functionSymbols) (m ^. predicateSymbols) (m ^. unaryOperators) (m ^. binaryOperators) (m ^. quantifiers) (m ^. firstOrder)

instance FromText RuleApplication where
  fromText :: Model -> Text -> Either Text RuleApplication
  fromText m txt = case fromText m txt :: Either Text Rule of
    Left e -> Left e
    Right r -> Right $ RuleApplication r []

tryParse :: forall a. (FromText a) => Model -> [(Text, Text)] -> Text -> ParseWrapper a
tryParse m replacements txt = case fromText m replacedTxt :: Either Text a of
  Left err -> Unparsed replacedTxt err
  Right result -> Parsed replacedTxt result
  where
    replacedTxt = foldr (\(alias, name) t -> replace alias name t) txt replacements

-----------------------------------------------------------------------------
updateModel :: Action -> Effect ROOT Model Action
updateModel (Drop LocationBin) = do
  dt <- use dragTarget
  case dt of
    Nothing -> pure ()
    Just addr -> proof %= lRemove addr
  io_ . consoleLog $ "dropped in bin"
updateModel (Drop (LocationAddr targetAddr pos)) = do
  m <- get
  use dragTarget >>= \case
    Nothing -> pure ()
    Just sourceAddr -> do
      io_ . consoleLog . ms $ "dropping (" ++ show sourceAddr ++ ") into (" ++ show targetAddr ++ ")"
      proof %= lMove targetAddr pos sourceAddr
  use spawnType >>= \case
    Nothing -> pure ()
    Just SpawnLine -> proof %=? lInsert (Right . ProofLine $ Derivation (tryParse m [] "Formula") (tryParse m [] "Rule")) targetAddr pos
    Just SpawnProof -> proof %=? lInsert (Right $ SubProof [] [] (Derivation (tryParse m [] "Formula") (tryParse m [] "Rule"))) targetAddr pos
    Just SpawnAssumption -> proof %=? lInsert (Left (tryParse m [] "Formula")) targetAddr pos
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
-- TODO and implement setSelectionRange:
-- https://developer.mozilla.org/en-US/docs/Web/API/HTMLInputElement/setSelectionRange
-- io_ . select . ms $ "proof-line" ++ show n
updateModel Blur = focusedLine .= Nothing
updateModel Nop = pure ()
updateModel (SpawnStart st) = spawnType .= Just st
updateModel (Input str) = do
  m <- get
  fline <- use focusedLine
  mapM_ (\addr -> proof %= lUpdateFormula (tryParse m (m ^. unaryOperators ++ m ^. binaryOperators ++ m ^. quantifiers) (fromMisoString str :: Text)) addr) fline

-----------------------------------------------------------------------------
viewModel :: Model -> View Model Action
viewModel model =
  H.div_
    []
    [ viewProof model,
      viewBin,
      viewSpawnNode SpawnLine "Insert Line",
      viewSpawnNode SpawnAssumption "Insert Assumption",
      viewSpawnNode SpawnProof "Insert Proof"
    ]

viewModelFirstOrder :: Model -> View Model Action
viewModelFirstOrder model =
  H.div_
    []
    [ viewProof model,
      viewBin,
      viewSpawnNode SpawnLine "Insert Line",
      viewSpawnNode SpawnAssumption "Insert Assumption",
      viewSpawnNode SpawnProof "Insert Proof"
    ]

-----------------------------------------------------------------------------