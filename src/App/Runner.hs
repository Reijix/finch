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
import Control.Monad (liftM2, liftM3, void, when)
import Control.Monad.RWS
import Control.Monad.State (MonadState (get), State)
import Control.Monad.State qualified as ST
import Data.Bifunctor (Bifunctor (first), bimap)
import Data.Either (fromLeft, fromRight)
import Data.Map (Map)
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
import Miso.Lens
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
      , events = dragEvents <> M.fromList [("dblclick", BUBBLE)] <> keyboardEvents <> defaultEvents
      }
 where
  m = initialModel proof unaryOperators binaryOperators quantifiers

-- TODO mapPAccumL such that I can take the line number with me...

mapP ::
  (MonadState Model m) =>
  (Assumption -> m Assumption) ->
  (Derivation -> m Derivation) ->
  Proof ->
  m Proof
mapP af df (ProofLine d) = ProofLine <$> df d
mapP af df (SubProof fs ps d) = liftM3 SubProof (mapM af fs) (mapM (mapP af df) ps) (df d)

type EffectState inner = RWS (ComponentInfo ROOT) [Schedule Action] Model inner

updateSymbols :: Effect ROOT Model Action
updateSymbols = do
  functionSymbols .= M.empty
  predicateSymbols .= M.empty
  proof <~ (use proof >>= mapP goFormula goLine)
 where
  goFormula :: Assumption -> EffectState Assumption
  goFormula a@(Unparsed{}) = pure a
  goFormula a =
    let (formula, txt) = (fromWrapper a, getText a)
     in do
          fsyms <- use functionSymbols
          psyms <- use predicateSymbols
          go fsyms psyms txt formula
   where
    go :: Map Text (Int, Pos) -> Map Text (Int, Pos) -> Text -> Formula -> EffectState Assumption
    go fsyms psyms txt formula@(Predicate name args) = case psyms M.!? name of
      Nothing -> do
        predicateSymbols %= M.insert name (length args, Pos (0, 0))
        return $ ParsedValid txt formula
      Just (n, pos) ->
        return $
          if n == length args
            then ParsedValid txt formula
            -- TODO error message
            else ParsedInvalid txt "error" formula
    go fsyms psyms txt (UnaryOp name formula) = go fsyms psyms txt formula <&> (<$>) (UnaryOp name)
    go fsyms psyms txt f@(BinaryOp name formula1 formula2) = do
      f1 <- go fsyms psyms txt formula1
      f2 <- go fsyms psyms txt formula2
      case f1 of
        (Unparsed _ err) -> return $ Unparsed txt err
        (ParsedInvalid _ err _) -> return $ ParsedInvalid txt err f
        (ParsedValid _ _) -> case f2 of
          (Unparsed _ err) -> return $ Unparsed txt err
          (ParsedInvalid _ err _) -> return $ ParsedInvalid txt err f
          (ParsedValid _ _) -> return $ ParsedValid txt f
    go fsyms psyms txt (Quantifier name variable formula) = go fsyms psyms txt formula <&> (<$>) (Quantifier name variable)
  goLine :: Derivation -> EffectState Derivation
  goLine (Derivation f r) = do
    f' <- goFormula f
    return $ Derivation f' r

-- | Main execution loop of the application.
updateModel :: Action -> Effect ROOT Model Action
-- Drag n Drop events
updateModel (Drop LocationBin) = do
  dt <- use dragTarget
  case dt of
    Nothing -> pure ()
    Just addr -> proof %= lRemove addr
updateModel (Drop (LocationAddr targetAddr pos)) = do
  m <- get
  use dragTarget >>= \case
    Nothing -> pure ()
    Just sourceAddr -> proof %= lMove targetAddr pos sourceAddr
  use spawnType >>= \case
    Nothing -> pure ()
    -- TODO adjust linenos
    Just SpawnLine -> proof %=? lInsert (Right . ProofLine $ Derivation (tryParse m [] (fromJust $ fromNodeAddr targetAddr (m ^. proof)) "Formula") (tryParse m [] (fromJust $ fromNodeAddr targetAddr (m ^. proof)) "Rule")) targetAddr pos
    Just SpawnProof -> proof %=? lInsert (Right $ SubProof [tryParse m [] (fromJust $ fromNodeAddr targetAddr (m ^. proof)) "Formula"] [] (Derivation (tryParse m [] 0 "Formula") (tryParse m [] (fromJust $ fromNodeAddr targetAddr (m ^. proof)) "Rule"))) targetAddr pos
    Just SpawnAssumption -> proof %=? lInsert (Left (tryParse m [] (fromJust $ fromNodeAddr targetAddr (m ^. proof)) "Formula")) targetAddr pos
updateModel (DragEnter a Before) = currentLineBefore .= Just a
updateModel (DragEnter a After) = currentLineAfter .= Just a
-- NOTE: the check for `Before` and `After` is actually needed, because processing order of events is not guaranteed.
updateModel (DragLeave Before) = currentLineBefore .= Nothing
updateModel (DragLeave After) = currentLineAfter .= Nothing
updateModel (SpawnStart st) = do
  spawnType .= Just st
  dragging .= True
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
updateModel Change = updateSymbols
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
  let p = tryParse m (m ^. unaryOperators ++ m ^. binaryOperators ++ m ^. quantifiers) (fromJust $ fromNodeAddr addr (m ^. proof)) (fromMisoString str :: Text) :: Wrapper Formula
  proof %= lUpdateFormula (const p) addr
  updateSymbols
  let delta = length (fromMisoString str :: String) - (length . T.unpack . getText $ p)
  -- restore selectionStart and selectionEnd (delta-adjusted)
  io_ $ setSelectionRange (ms $ "proof-line" ++ show (fromJust (fromNodeAddr addr (m ^. proof)))) (start - delta) (end - delta)
updateModel (ProcessInput str start end (Right addr)) = do
  m <- get
  let r = tryParse m (m ^. unaryOperators ++ m ^. binaryOperators ++ m ^. quantifiers) (fromJust $ fromNodeAddr addr (m ^. proof)) (fromMisoString str :: Text) :: Wrapper RuleApplication
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
  update :: Model -> Text -> Either (Wrapper Formula) (Wrapper RuleApplication)
  update m txt =
    let (first, rest) = T.splitAt start txt
        (second, third) = T.splitAt (end - start) rest
        newTxt = T.concat [first, "(", second, ")", third]
     in case eaddr of
          Left addr -> Left $ tryParse m (m ^. unaryOperators ++ m ^. binaryOperators ++ m ^. quantifiers) (fromJust $ fromNodeAddr addr (m ^. proof)) newTxt
          Right addr -> Right $ tryParse m (m ^. unaryOperators ++ m ^. binaryOperators ++ m ^. quantifiers) (fromJust $ fromNodeAddr addr (m ^. proof)) newTxt
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
  fromText :: Model -> Int -> Text -> Either Text a

instance FromText Rule where
  fromText :: Model -> Int -> Text -> Either Text Rule
  fromText m n str = Right $ Rule str [] (Predicate "" [])

instance FromText Formula where
  fromText :: Model -> Int -> Text -> Either Text Formula
  fromText m = parseFormula (m ^. unaryOperators) (m ^. binaryOperators) (m ^. quantifiers)

instance FromText RuleApplication where
  fromText :: Model -> Int -> Text -> Either Text RuleApplication
  fromText _ = parseRuleApplication

{- | Wrapper for `fromText` that also takes a list of aliases and
tries to replace these aliases in the `Text`
-}
tryParse :: forall a. (FromText a) => Model -> [(Text, Text)] -> Int -> Text -> Wrapper a
tryParse m replacements n txt = case fromText m n replacedTxt :: Either Text a of
  Left err -> Unparsed replacedTxt err
  Right result -> ParsedValid replacedTxt result
 where
  replacedTxt = foldr (\(alias, name) t -> T.replace alias name t) txt replacements
