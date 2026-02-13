-----------------------------------------------------------------------------
module App.Runner (
  runApp,
  initialModel,
  checkProof,
  tryParse,
  Proof (..),
  FromText (..),
  Model (..),
  Derivation (..),
) where

-----------------------------------------------------------------------------
import App.Model
import App.Views
import Data.Text qualified as T
import Fitch.Proof
import Fitch.Verification (verifyProof)
import Miso (
  App,
  CSS (Href),
  Component (..),
  ComponentInfo,
  DOMRef,
  Effect,
  KeyInfo (keyCode, shiftKey),
  MisoString,
  Phase (..),
  PointerEvent (client),
  ROOT,
  Schedule,
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
  select,
  setSelectionRange,
  startApp,
  startSub,
  stopSub,
  text,
 )
import Miso.DSL (jsg, (#))
import Miso.Effect (Sub)
import Miso.Html.Element qualified as H
import Miso.Html.Property qualified as HP
import Miso.Lens
import Miso.Subscription.Util (createSub)
import Miso.Svg (text_)
import Parser.Formula (parseFormula)
import Parser.Rule (parseRuleApplication)
import Relude.Extra.Newtype

-----------------------------------------------------------------------------

-- * Application Loop

{- | `runApp` @proof@ @unaryOperators@ @binaryOperators@ @quantifiers@

Runs the fitch-editor app with a given initial @proof@,
a list of unary operators, binary operators and quantifiers.
-}
runApp ::
  -- | Initial proof
  Proof ->
  -- | List of operators with aliases (alias, operator, arity)
  [(Text, Text, Int)] ->
  -- | List of quantifiers with aliases (alias, operator)
  [(Text, Text)] ->
  -- | List of infix predicates with aliases (alias, predicate)
  [(Text, Text)] ->
  -- | A map that contains all rules, mapping their names to their specification
  Map Name RuleSpec ->
  -- | Resulting program
  IO ()
runApp proof operators infixPreds quantifiers rules =
  startApp (dragEvents <> fromList [("dblclick", BUBBLE)] <> keyboardEvents <> defaultEvents) $
    (component m updateModel viewModel)
      { styles = [Href "style.css"]
      , mount = Just Setup
      }
 where
  m = initialModel proof operators infixPreds quantifiers rules

checkProof :: forall m. (MonadState Model m) => m ()
checkProof = do
  regenerateSymbols
  checkFreshness
  ruleMap <- use rules
  proof %= verifyProof ruleMap

clearDrag :: Effect ROOT Model Action
clearDrag = do
  currentHoverLine .= Nothing
  dragging .= False
  dragTarget .= Nothing
  spawnType .= Nothing

dropInto :: NodeAddr -> Effect ROOT Model Action
dropInto targetAddr = do
  m <- get
  use dragTarget >>= \case
    Nothing -> pass
    Just (Left na) -> proof %= naMoveBefore targetAddr na
    Just (Right pa) -> proof %= paMoveBefore targetAddr pa
  use spawnType >>= \case
    Nothing -> pass
    -- TODO adjust linenos
    Just SpawnLine -> do
      mp <-
        naInsertBefore
          (Right . Left $ Derivation (tryParse m 999 "") (tryParse m 999 "(?)"))
          targetAddr
          <$> use proof
      case mp of
        Just (Left na, p) -> do
          proof .= p
          setFocus (Left targetAddr)
        _ -> pass
    Just SpawnProof -> do
      mp <-
        naInsertBefore
          ( Right . Right $
              SubProof [] [] (Derivation (tryParse m 999 "") (tryParse m 999 "(?)"))
          )
          targetAddr
          <$> use proof
      case mp of
        Just (Right pa, p) -> do
          proof .= p
          setFocus (Left $ naFromPA pa NAConclusion)
        _ -> pass
  clearDrag
  checkProof

setFocus :: Either NodeAddr NodeAddr -> Effect ROOT Model Action
setFocus ea = do
  focusedLine .= Just ea
  p <- use proof
  case ea of
    Left a -> selectFocus ("proof-line" <> show (lineNoOr999 a p))
    Right a -> selectFocus ("proof-line-rule" <> show (lineNoOr999 a p))
 where
  selectFocus :: MisoString -> Effect ROOT Model Action
  selectFocus str = do
    io_ $ focus str
    io_ $ select str

-- | Main execution loop of the application.
updateModel :: Action -> Effect ROOT Model Action
updateModel Setup = checkProof
------------------------------------
-- Drag n Drop events
updateModel (Drop LocationBin) = do
  dt <- use dragTarget
  case dt of
    Nothing -> pass
    Just (Left na) -> proof %= naRemove na
    Just (Right pa) -> proof %= paRemove pa
  clearDrag
updateModel (Drop (LocationAddr targetAddr)) = dropInto targetAddr
updateModel (DragEnter na) = do
  p <- use proof
  use spawnType
    >>= \case
      Just (canSpawnIn na -> True) ->
        currentHoverLine .= Just na
      Just (canSpawnIn na -> False) ->
        currentHoverLine .= Nothing
      Nothing ->
        use dragTarget >>= \case
          Just (naCanMoveBefore na -> True) -> currentHoverLine .= Just na
          _ -> currentHoverLine .= Nothing
updateModel DragLeave = currentHoverLine .= Nothing
updateModel (SpawnStart st) = do
  spawnType .= Just st
  dragging .= True
updateModel (DragStart dt) = do
  dragTarget .= Just dt
  dragging .= True
updateModel DragEnd = do
  chl <- use currentHoverLine
  maybe clearDrag dropInto chl
------------------------------------
-- Input related events
updateModel (DoubleClick ea) = setFocus ea
updateModel Blur = focusedLine .= Nothing
updateModel Change = checkProof
updateModel (Input str ref) = do
  m <- get
  fline <- use focusedLine
  -- save selectionStart and selectionEnd
  case fline of
    Nothing -> pass
    Just addr -> io $ do
      Just (start :: Int) <- castJSVal =<< getProperty ref "selectionStart"
      Just (end :: Int) <- castJSVal =<< getProperty ref "selectionEnd"
      pure $ ProcessInput str start end addr
  checkProof
updateModel (ProcessInput str start end (Left addr)) = do
  m <- get
  f <-
    if isNAAssumption addr
      then do
        let a =
              tryParse
                m
                (lineNoOr999 addr (m ^. proof))
                (fromMisoString str) ::
                Assumption
        proof %= naUpdateFormula (Left $ const a) addr
        pure $ un a
      else do
        let f =
              tryParse
                m
                (lineNoOr999 addr (m ^. proof))
                (fromMisoString str) ::
                Formula
        proof %= naUpdateFormula (Right $ const f) addr
        pure f

  checkProof
  let delta = T.length (fromMisoString str) - (T.length . getText $ f)
  -- restore selectionStart and selectionEnd (delta-adjusted)
  io_ $
    setSelectionRange
      ( ms $
          "proof-line"
            ++ show (lineNoOr999 addr (m ^. proof))
      )
      (start - delta)
      (end - delta)
updateModel (ProcessInput str start end (Right addr)) = do
  m <- get
  let r =
        tryParse
          m
          (lineNoOr999 addr (m ^. proof))
          (fromMisoString str) ::
          Wrapper RuleApplication
  proof %= naUpdateRule (const r) addr
  checkProof
  let delta = T.length (fromMisoString str) - (T.length . getText $ r)
  -- restore selectionStart and selectionEnd (delta-adjusted)
  io_ $
    setSelectionRange
      ( ms $
          "proof-line-rule"
            ++ show (lineNoOr999 addr (m ^. proof))
      )
      (start - delta)
      (end - delta)
updateModel (ProcessParens eaddr start end) = do
  m <- get
  p <- use proof
  case eaddr of
    Left addr ->
      proof %= naUpdateFormula (Right $ \p -> fromLeft p $ update m (getText p)) addr
    Right addr ->
      proof %= naUpdateRule (\r -> fromRight r $ update m (getText r)) addr
  checkProof
 where
  update :: Model -> Text -> Either Formula (Wrapper RuleApplication)
  update m txt =
    let (first, rest) = T.splitAt start txt
        (second, third) = T.splitAt (end - start) rest
        newTxt = T.concat [first, "(", second, ")", third]
     in case eaddr of
          Left addr ->
            Left $
              tryParse
                m
                (lineNoOr999 addr (m ^. proof))
                newTxt
          Right addr ->
            Right $
              tryParse
                m
                (lineNoOr999 addr (m ^. proof))
                newTxt
updateModel (KeyDownStart addr ref) = startSub ("keyDownSub" ++ show addr) (onKeyDownSub addr ref)
updateModel (KeyDownStop addr) = stopSub ("keyDownSub" ++ show addr)
------------------------------------
updateModel Nop = pass

-- | Takes a `Model` and returns the corresponding `View`.
viewModel :: Model -> View Model Action
viewModel model =
  H.div_
    [HP.class_ "fitch-container"]
    [ H.div_
        [HP.class_ "button-container"]
        [ viewBin
        , viewSpawnNode SpawnLine "+Line"
        , viewSpawnNode SpawnProof "+Proof"
        ]
    , viewProof model
    ]

-----------------------------------------------------------------------------

-- * Subscriptions

{- | Subscription for the 'onkeydown' event.

Used for detecting presses of '(' and 'Enter'.
* On 'Enter' fires the `Blur` event,
* On '(' inserts the closing parenthesis at the end of selection.
-}
onKeyDownSub :: Either NodeAddr NodeAddr -> DOMRef -> Sub Action
onKeyDownSub addr domRef = createSub acquire (const pass)
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
        -- select all text, replace it with the new text, and adjust cursorition
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
  fromText :: Model -> Int -> Text -> Either Text a

instance FromText RawFormula where
  fromText :: Model -> Int -> Text -> Either Text RawFormula
  fromText m = parseFormula False (m ^. operators) (m ^. infixPreds) (m ^. quantifiers)

instance FromText RawAssumption where
  fromText :: Model -> Int -> Text -> Either Text RawAssumption
  fromText m n = fmap RawAssumption . parseFormula True (m ^. operators) (m ^. infixPreds) (m ^. quantifiers) n

instance FromText RuleApplication where
  fromText :: Model -> Int -> Text -> Either Text RuleApplication
  fromText _ = parseRuleApplication

{- | Wrapper for `fromText` that also takes a list of aliases and
tries to replace these aliases in the `Text`
-}
tryParse ::
  forall a.
  (FromText a) =>
  Model -> Int -> Text -> Wrapper a
tryParse m n txt = case fromText m n replacedTxt :: Either Text a of
  Left err -> Unparsed replacedTxt err
  Right result -> ParsedValid replacedTxt result
 where
  replacedTxt =
    foldr
      (\(alias, name) t -> T.replace alias name t)
      (foldr (\(alias, name, _) t -> T.replace alias name t) txt (m ^. operators))
      (m ^. quantifiers)
