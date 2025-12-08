-----------------------------------------------------------------------------
module App.Runner (
  runApp,
  initialModel,
  tryParse,
  Proof (..),
  FromText (..),
  Model (..),
  Derivation (..),
) where

-----------------------------------------------------------------------------
import App.Model
import App.Views
import Control.Monad (void, when)
import Control.Monad.State
import Data.Either (fromLeft, fromRight)
import Data.Map qualified as M
import Data.Maybe (fromJust, fromMaybe)
import Data.Text (Text)
import Data.Text qualified as T
import Fitch.Proof
import Language.Javascript.JSaddle
import Miso (
  App,
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
  callFunction,
  castJSVal,
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
  getProperty,
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
import Miso.Effect (Sub)
import Miso.Html.Element qualified as H
import Miso.Html.Property qualified as HP
import Miso.Lens (Lens, use, (%=), (.=), (^.))
import Miso.Subscription.Util (createSub)
import Miso.Svg (text_)
import Parser.Formula (parseFormula)
import Parser.Rule (parseRuleApplication)

-----------------------------------------------------------------------------

-- * Application Loop

{- | `runApp` @proof@ @unaryOperators@ @binaryOperators@ @quantifiers@

Runs the fitch-editor app with a given initial @proof@,
a list of unary operators, binary operators and quantifiers.
-}
runApp ::
  -- | Initial proof
  Proof ->
  -- | List of unary operators with aliases (alias, operator)
  [(Text, Text)] ->
  -- | List of binary operators with aliases (alias, operator)
  [(Text, Text)] ->
  -- | List of quantifiers with aliases (alias, operator)
  [(Text, Text)] ->
  -- | Resulting program
  IO ()
runApp proof unaryOperators binaryOperators quantifiers =
  run . startApp $
    (component m updateModel viewModel)
      { styles = [Href "style.css"]
      , events = dragEvents <> M.fromList [("dblclick", False)] <> keyboardEvents <> defaultEvents
      }
 where
  m = initialModel proof unaryOperators binaryOperators quantifiers

-- | Main execution loop of the application.
updateModel :: Action -> Effect ROOT Model Action
-- Drag n Drop events
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
    Just SpawnProof -> do
      proof %=? lInsert (Right $ SubProof [tryParse m [] "Formula"] [] (Derivation (tryParse m [] "Formula") (tryParse m [] "Rule"))) targetAddr pos
      p <- use proof
      io_ $ consoleLog $ ms $ show p
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
------------------------------------
-- Input related events
updateModel (DoubleClick ea) = do
  focusedLine .= Just ea
  p <- use proof
  case ea of
    Left a -> do
      io_ . focus . ms $ "proof-line" ++ show (fromJust (fromNodeAddr a p))
      io_ . select . ms $ "proof-line" ++ show (fromJust (fromNodeAddr a p))
    Right a -> do
      io_ . focus . ms $ "proof-line-rule" ++ show (fromJust (fromNodeAddr a p))
      io_ . select . ms $ "proof-line-rule" ++ show (fromJust (fromNodeAddr a p))
updateModel Blur = focusedLine .= Nothing
updateModel (SpawnStart st) = spawnType .= Just st
updateModel (Input str ref) = do
  m <- get
  fline <- use focusedLine
  -- save selectionStart and selectionEnd
  case fline of
    Nothing -> return ()
    Just addr -> io $ do
      Just (start :: Int) <- castJSVal =<< getProperty ref "selectionStart"
      Just (end :: Int) <- castJSVal =<< getProperty ref "selectionEnd"
      return $ ProcessInput str start end addr
updateModel (ProcessInput str start end (Left addr)) = do
  m <- get
  let p = tryParse m (m ^. unaryOperators ++ m ^. binaryOperators ++ m ^. quantifiers) (fromMisoString str :: Text) :: ParseWrapper Formula
  proof %= lUpdateFormula (const p) addr
  let delta = length (fromMisoString str :: String) - (length . T.unpack . getText $ p)
  -- restore selectionStart and selectionEnd (delta-adjusted)
  io_ $ setSelectionRange (ms $ "proof-line" ++ show (fromJust (fromNodeAddr addr (m ^. proof)))) (start - delta) (end - delta)
updateModel (ProcessInput str start end (Right addr)) = do
  m <- get
  let r = tryParse m (m ^. unaryOperators ++ m ^. binaryOperators ++ m ^. quantifiers) (fromMisoString str :: Text) :: ParseWrapper RuleApplication
  proof %= lUpdateRule (const r) addr
  let delta = length (fromMisoString str :: String) - (length . T.unpack . getText $ r)
  -- restore selectionStart and selectionEnd (delta-adjusted)
  io_ $ setSelectionRange (ms $ "proof-line-rule" ++ show (fromJust (fromNodeAddr addr (m ^. proof)))) (start - delta) (end - delta)
updateModel (ProcessParens eaddr start end) = do
  m <- get
  p <- use proof
  case eaddr of
    Left addr ->
      proof %= lUpdateFormula (\p -> fromLeft p $ update m (getText p)) addr
    Right addr ->
      proof %= lUpdateRule (\r -> fromRight r $ update m (getText r)) addr
 where
  update :: Model -> Text -> Either (ParseWrapper Formula) (ParseWrapper RuleApplication)
  update m txt =
    let (first, rest) = T.splitAt start txt
        (second, third) = T.splitAt (end - start) rest
        newTxt = T.concat [first, "(", second, ")", third]
     in case eaddr of
          Left addr -> Left $ tryParse m (m ^. unaryOperators ++ m ^. binaryOperators ++ m ^. quantifiers) newTxt
          Right addr -> Right $ tryParse m (m ^. unaryOperators ++ m ^. binaryOperators ++ m ^. quantifiers) newTxt
updateModel (KeyDownStart addr ref) = startSub ("keyDownSub" ++ show addr) (onKeyDownSub addr ref)
updateModel (KeyDownStop addr) = stopSub ("keyDownSub" ++ show addr)
------------------------------------
updateModel Nop = pure ()

-- | Takes a `Model` and returns the corresponding `View`.
viewModel :: Model -> View Model Action
viewModel model =
  H.div_
    []
    [ viewProof model
    , viewBin
    , viewSpawnNode SpawnLine "Insert Line"
    , viewSpawnNode SpawnAssumption "Insert Assumption"
    , viewSpawnNode SpawnProof "Insert Proof"
    ]

-----------------------------------------------------------------------------

-- * Subscriptions

{- | Subscription for the 'onkeydown' event.

Used for detecting presses of '(' and 'Enter'.
* On 'Enter' fires the `Blur` event,
* On '(' inserts the closing parenthesis at the end of selection.
-}
onKeyDownSub :: Either NodeAddr NodeAddr -> DOMRef -> Sub Action
onKeyDownSub addr domRef = createSub acquire (removeEventListener domRef "keydown")
 where
  acquire = do
    addEventListener domRef "keydown" $ \evt -> do
      Just (keyCode :: Int) <- castJSVal =<< getProperty evt "keyCode"
      Just (shiftKey :: Bool) <- castJSVal =<< getProperty evt "shiftKey"
      Just (start :: Int) <- castJSVal =<< getProperty domRef "selectionStart"
      Just (end :: Int) <- castJSVal =<< getProperty domRef "selectionEnd"

      -- when '(' is pressed, insert closing parenthesis as well
      when (keyCode == 57 && shiftKey && start < end) $ void $ do
        -- prevent call of the `input` event.
        eventPreventDefault evt
        -- split current value into parts, to insert the parentheses
        Just (value :: Text) <- castJSVal =<< getProperty domRef "value"
        let (first, rest) = T.splitAt start value
            (second, third) = T.splitAt (end - start) rest
            newTxt = T.concat [first, "(", second, ")", third]
        -- select all text, replace it with the new text, and adjust cursor position
        doc <- jsg "document"
        domRef # "select" $ ()
        -- NOTE: execCommand is deprecated, however its use is still recommended
        --       for inserting text to <input> while keeping the history intact.
        doc # "execCommand" $ ("insertText", False, newTxt)
        domRef # "setSelectionRange" $ (end + 2, end + 2, "none")

      -- when 'Enter' is pressed, call blur on the element, to lose focus
      when (keyCode == 13) $ void $ callFunction domRef "blur" ()

-----------------------------------------------------------------------------

-- * Utilities

(%=?) :: (MonadState record m) => Lens record field -> (field -> Maybe field) -> m ()
(%=?) _lens f = _lens %= (\x -> fromMaybe x (f x))

-- | Class for parsing `Text`
class FromText a where
  {- | Takes a `Model` and some `Text` and tries to parse it to the desired type.
  On failure returns an error message.
  -}
  fromText :: Model -> Text -> Either Text a

instance FromText Rule where
  fromText :: Model -> Text -> Either Text Rule
  fromText m str = Right $ Rule str [] (Predicate "" [])

instance FromText Formula where
  fromText :: Model -> Text -> Either Text Formula
  fromText m = parseFormula (m ^. unaryOperators) (m ^. binaryOperators) (m ^. quantifiers)

instance FromText RuleApplication where
  fromText :: Model -> Text -> Either Text RuleApplication
  fromText _ = parseRuleApplication

{- | Wrapper for `fromText` that also takes a list of aliases and
tries to replace these aliases in the `Text`
-}
tryParse :: forall a. (FromText a) => Model -> [(Text, Text)] -> Text -> ParseWrapper a
tryParse m replacements txt = case fromText m replacedTxt :: Either Text a of
  Left err -> Unparsed replacedTxt err
  Right result -> Parsed replacedTxt result
 where
  replacedTxt = foldr (\(alias, name) t -> T.replace alias name t) txt replacements
