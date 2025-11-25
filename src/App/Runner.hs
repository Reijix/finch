module App.Runner (runApp, runAppFirstOrder, Proof (..), FromString (..), Model (..), Derivation (..)) where

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
import Parser.Formula

(%=?) :: (MonadState record m) => Lens record field -> (field -> Maybe field) -> m ()
(%=?) _lens f = _lens %= (\x -> fromMaybe x (f x))

-----------------------------------------------------------------------------

-- | Test of Haddock
runApp :: Proof -> [String] -> [String] -> IO ()
runApp p unaryOperators binaryOperators =
  run . startApp $
    (component m updateModel viewModel)
      { styles = [Href "style.css"],
        events = dragEvents <> M.fromList [("dblclick", False), ("focusout", False)] <> keyboardEvents <> defaultEvents
      }
  where
    m = initialModel p unaryOperators binaryOperators

runAppFirstOrder :: Proof -> [(String, Int)] -> [(String, Int)] -> [String] -> [String] -> [String] -> IO ()
runAppFirstOrder p functionSymbols predicateSymbols unaryOperators binaryOperators quantifiers =
  run . startApp $
    (component m updateModel viewModelFirstOrder)
      { styles = [Href "style.css"],
        events = dragEvents <> M.fromList [("dblclick", False), ("focusout", False)] <> keyboardEvents <> defaultEvents
      }
  where
    m = initialModelFirstOrder p functionSymbols predicateSymbols unaryOperators binaryOperators quantifiers

-----------------------------------------------------------------------------
class FromString a where
  fromString :: Model -> String -> Either String a

instance FromString Rule where
  fromString :: Model -> String -> Either String Rule
  fromString m str = Right $ Rule str [] (Predicate "" [])

instance FromString Formula where
  fromString :: Model -> String -> Either String Formula
  fromString m = parseFormula (m ^. functionSymbols) (m ^. predicateSymbols) (m ^. unaryOperators) (m ^. binaryOperators) (m ^. quantifiers) (m ^. firstOrder)

instance FromString RuleApplication where
  fromString :: Model -> String -> Either String RuleApplication
  fromString m str = case fromString m str :: Either String Rule of
    Left e -> Left e
    Right r -> Right $ RuleApplication r []

tryParse :: forall a. (FromString a) => Model -> String -> ParseWrapper a
tryParse m str = case fromString m str :: Either String a of
  Left err -> Unparsed str err
  Right result -> Parsed str result

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
    Just SpawnLine -> proof %=? lInsert (Right . ProofLine $ Derivation (tryParse m "Formula") (tryParse m "Rule")) targetAddr pos
    Just SpawnProof -> proof %=? lInsert (Right $ SubProof [] [] (Derivation (tryParse m "Formula") (tryParse m "Rule"))) targetAddr pos
    Just SpawnAssumption -> proof %=? lInsert (Left (tryParse m "Formula")) targetAddr pos
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
updateModel Blur = focusedLine .= Nothing
updateModel Nop = pure ()
updateModel (SpawnStart st) = spawnType .= Just st
-- TODO: Maybe actual parse should only happen on enter, i.e. when `blur` fires.
updateModel (Input str) = do
  m <- get
  fline <- use focusedLine
  mapM_ (\addr -> proof %= lUpdateFormula (tryParse m (fromMisoString str :: String)) addr) fline

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