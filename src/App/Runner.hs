module App.Runner (runApp, runAppFirstOrder, initialModel, initialModelFirstOrder, tryParse, Proof (..), FromText (..), Model (..), Derivation (..)) where

import App.Model
import App.Views
import Control.Monad (when)
import Control.Monad.State
import Data.Map qualified as M
import Data.Maybe (fromJust, fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Fitch.Proof
import Language.Javascript.JSaddle
import Miso
  ( App,
    CSS (Href),
    Component (events, styles, subs),
    DOMRef,
    Effect,
    KeyInfo (keyCode, shiftKey),
    MisoString,
    PointerEvent (client),
    ROOT,
    View,
    addEventListener,
    component,
    consoleLog,
    defaultEvents,
    defaultOptions,
    dispatchEvent,
    dragEvents,
    emptyDecoder,
    eventPreventDefault,
    focus,
    fromMisoString,
    getElementById,
    io,
    io_,
    issue,
    keyboardEvents,
    mouseSub,
    ms,
    newEvent,
    preventDefault,
    removeEventListener,
    run,
    select,
    setSelectionRange,
    startApp,
    startSub,
    stopSub,
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
import Miso.Subscription.Util (createSub)
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
  fromText m = parseFormula (m ^. unaryOperators) (m ^. binaryOperators) (m ^. quantifiers)

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
    replacedTxt = foldr (\(alias, name) t -> T.replace alias name t) txt replacements

-----------------------------------------------------------------------------
onKeyDownSub :: NodeAddr -> DOMRef -> Sub Action
onKeyDownSub addr domRef sink = createSub acquire (removeEventListener domRef "keydown") sink
  where
    acquire = do
      addEventListener domRef "keydown" $ \evt -> do
        Just (keyCode :: Int) <- fromJSVal =<< evt ! ("keyCode" :: MisoString)
        Just shiftKey <- fromJSVal =<< evt ! ("shiftKey" :: MisoString)
        start :: Int <- fromJSValUnchecked =<< (domRef ! "selectionStart")
        end :: Int <- fromJSValUnchecked =<< (domRef ! "selectionEnd")
        when (keyCode == 57 && shiftKey && start < end) $ do
          eventPreventDefault evt
          value :: Text <- fromJSValUnchecked =<< (domRef ! "value")
          let (first, rest) = T.splitAt start value
              (second, third) = T.splitAt (end - start) rest
              newTxt = T.concat [first, "(", second, ")", third]
          -- domRef # "setSelectionRange" $ (end + 2, end + 2, "none")
          sink (ProcessInput (ms newTxt) (end + 2) (end + 2) addr)
        when (keyCode == 13) $ sink Blur

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
  io_ . select . ms $ "proof-line" ++ show (fromJust (fromNodeAddr a p))
updateModel Blur = focusedLine .= Nothing
updateModel Nop = pure ()
updateModel (SpawnStart st) = spawnType .= Just st
updateModel (Input str ref) = do
  m <- get
  fline <- use focusedLine
  -- save selectionStart and selectionEnd
  case fline of
    Nothing -> return ()
    Just addr -> io $ do
      start :: Int <- fromJSValUnchecked =<< (ref ! "selectionStart")
      end :: Int <- fromJSValUnchecked =<< (ref ! "selectionEnd")
      return $ ProcessInput str start end addr
updateModel (ProcessInput str start end addr) = do
  m <- get
  let p = tryParse m (m ^. unaryOperators ++ m ^. binaryOperators ++ m ^. quantifiers) (fromMisoString str :: Text) :: ParseWrapper Formula
  proof %= lUpdateFormula (const p) addr
  let delta = length (fromMisoString str :: String) - (length . T.unpack . getText $ p)
  -- restore selectionStart and selectionEnd (delta-adjusted)
  io_ $ setSelectionRange (ms $ "proof-line" ++ show (fromJust (fromNodeAddr addr (m ^. proof)))) (start - delta) (end - delta)
updateModel (ProcessParens a start end) = do
  m <- get
  p <- use proof
  proof %= lUpdateFormula (update m) a
  where
    update :: Model -> ParseWrapper Formula -> ParseWrapper Formula
    update m p =
      let txt = getText p
          (first, rest) = T.splitAt start txt
          (second, third) = T.splitAt (end - start) rest
          newTxt = T.concat [first, "(", second, ")", third]
       in tryParse m (m ^. unaryOperators ++ m ^. binaryOperators ++ m ^. quantifiers) newTxt
updateModel (KeyDownStart addr ref) = startSub ("keyDownSub" ++ show addr) (onKeyDownSub addr ref)
updateModel (KeyDownStop addr) = stopSub ("keyDownSub" ++ show addr)

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