{- |
Module      : App.Update
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (GHCJS)

The update loop of the application, basically all of its logic.
-}
module App.Update (
  updateModel,
  checkProof,
  tryParse,
) where

-----------------------------------------------------------------------------
import App.Decoder
import App.Model
import App.Views
import Data.IntSet (isSubsetOf)
import Data.Text qualified as T
import Fitch.Proof
import Fitch.Verification (checkFreshness, regenerateSymbols, verifyProof)
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
  ToJSVal (toJSVal),
  URI (..),
  View,
  addEventListener,
  callFunction,
  castJSVal,
  component,
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
  getURI,
  io,
  io_,
  isNull,
  issue,
  keyboardEvents,
  mouseEvents,
  mouseSub,
  ms,
  newEvent,
  preventDefault,
  pushURI,
  removeEventListener,
  replaceURI,
  select,
  setSelectionRange,
  startApp,
  startSub,
  stopSub,
  text,
  touchEvents,
  uriSub,
  withSink,
 )
import Miso.DSL (jsg, (#))
import Miso.Effect (Sub)
import Miso.FFI.QQ (js)
import Miso.Html.Element qualified as H
import Miso.Html.Property qualified as HP
import Miso.Lens (Lens, LensCore (_get), use, (%=), (.=), (<~), (^.))
import Miso.Subscription.Util (createSub)
import Miso.Svg (text_)
import Parser.Formula (
  FormulaParserState (FormulaParserState),
  parseAssumption,
  parseFormula,
 )
import Parser.Proof (parseProof)
import Parser.Rule (parseRuleApplication)
import Relude.Extra.Map (insert, member, (!?))
import Util

-----------------------------------------------------------------------------

-- * Update loop

-- | Main execution loop of the application.
updateModel :: Action -> Effect ROOT Model Action
------------------------------------
-- Setup events
updateModel Setup = proofReparse >> updateProof
updateModel (InitMathJAX domRef) = io_ [js| MathJax.typesetPromise([${domRef}]); |]
updateModel (SetProof p) = do
  proof .= p
  proofReparse
  updateProof
------------------------------------
-- 'URI' event
updateModel (PopState uri) = do
  readURI uri >> proofReparse >> checkProof >> updateTitle
------------------------------------
-- Events that toggle UI elements
updateModel (PopOpen name True) =
  use dragging >>= \case
    True -> pass
    False -> io_ $ showPopover name
updateModel (PopOpen _ False) = pass
updateModel (PopClose name) = io_ $ hidePopover name
updateModel ToggleSidebar = sidebarToggle %= not
------------------------------------
-- Drag n Drop events
updateModel (Drop LocationBin) = do
  dt <- use dragTarget
  case dt of
    Nothing -> pass
    Just (Left na) -> proof %=? naRemove na
    Just (Right pa) -> proof %=? paRemove pa
  clearDrag >> updateProof
updateModel (Drop (LineAddr targetAddr)) = dropBeforeLine targetAddr
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
          Just (naCanMoveBefore p na -> True) -> currentHoverLine .= Just na
          _ -> currentHoverLine .= Nothing
updateModel DragLeave = currentHoverLine .= Nothing
updateModel (SpawnStart st) = do
  spawnType .= Just st
  dragging .= True
updateModel (DragStart dt) = do
  dragTarget .= Just dt
  p <- use proof
  whenLeftM_ (pure dt) $ \na -> io_ $ hidePopover ("formula-error-" <> show (lineNoOr999 na p))
  dragging .= True
updateModel DragEnd = do
  chl <- use currentHoverLine
  whenJust chl dropBeforeLine
  clearDrag
------------------------------------
-- Input related events
updateModel (FocusInput ea) = do
  fline <- use focusedLine
  if fline /= Just ea
    then
      setFocus ea
    else pass
updateModel (Blur ea) = do
  fline <- use focusedLine
  focusedLine .= if fline == Just ea then Nothing else fline
updateModel Change = updateProof
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
updateModel (ProcessInput str start end eaddr) = do
  m <- get
  (identifier, len) <- case eaddr of
    Left addr -> do
      if isNestedNAAssumption addr
        then do
          let a =
                tryParse
                  m
                  (lineNoOr999 addr (m ^. proof))
                  (fromMisoString str) ::
                  Wrapper RawAssumption
          proof %=? naUpdateFormula (Left (\(_, r) -> (a, r))) addr
          pure (mkFormulaInputId addr (m ^. proof), T.length . getText $ a)
        else do
          let f =
                tryParse
                  m
                  (lineNoOr999 addr (m ^. proof))
                  (fromMisoString str) ::
                  Formula
          proof %=? naUpdateFormula (Right $ const f) addr
          pure (mkFormulaInputId addr (m ^. proof), T.length . getText $ f)
    Right addr -> do
      let r =
            tryParse
              m
              (lineNoOr999 addr (m ^. proof))
              (fromMisoString str) ::
              Wrapper RuleApplication
      proof %=? naUpdateRule (const r) addr
      pure (mkRuleInputId addr (m ^. proof), T.length . getText $ r)

  checkProof
  let delta = T.length (fromMisoString str) - len
  -- restore selectionStart and selectionEnd (delta-adjusted)
  when (delta /= 0) $
    io_ $
      setSelectionRange
        identifier
        (start - delta)
        (end - delta)
------------------------------------
updateModel Nop = pass

-----------------------------------------------------------------------------

-- * Effects

{- | Re-checks a 'Proof', i.e. runs the verifier, updates the 'URI' and document title.

Should be called after every change to the 'Proof'.
-}
updateProof :: Effect ROOT Model Action
updateProof = checkProof >> updateURI >> updateTitle

{- | Updates the @document.title@ to show how many errors there are and
what the conclusion of the 'Proof' is.
-}
updateTitle :: Effect ROOT Model Action
updateTitle = do
  p@(SubProof _ _ (Derivation f _)) <- use proof
  let title =
        ( case proofErrors p of
            0 -> mempty
            1 -> "(1) "
            n -> "(" <> show n <> ") "
        )
          <> prettyPrint f
  io_ [js| document.title = ${title} |]

{- | Runs the 'Proof' verification algorithm, i.e.

1. Checks that symbols only occur with the same arity
2. Checks freshness 'Assumption's
3. Verifies all 'RuleApplication's.
-}
checkProof :: forall m. (MonadState Model m) => m ()
checkProof = do
  p <- use proof
  ruleMap <- use rules
  let (fsymbs, psymbs, p') = regenerateSymbols p
      p'' = checkFreshness p'
      p''' = verifyProof ruleMap p''
  functionSymbols .= fsymbs
  predicateSymbols .= psymbs
  proof .= p'''

-- | To be called after dragging ends, resets all drag parameters.
clearDrag :: Effect ROOT Model Action
clearDrag = do
  currentHoverLine .= Nothing
  dragging .= False
  dragTarget .= Nothing
  spawnType .= Nothing

-- | Takes a 'URI' and reads in a proof if it contains one.
readURI :: URI -> Effect ROOT Model Action
readURI uri = do
  case uriQueryString uri !? "proof" of
    Just (Just str) -> case decodeFromUrl (fromMisoString str :: Text) of
      Nothing -> pass
      Just (p :: Proof) -> proof .= p
    _ -> pass

-- | Updates the 'URI' to reflect the current 'Proof'.
updateURI :: Effect ROOT Model Action
updateURI = do
  p <- use proof
  io_ $ do
    uri <- getURI
    let newURI = uri{uriQueryString = insert "proof" (Just . ms $ encodeForUrl p) (uriQueryString uri)}
    if uri /= newURI then pushURI newURI else pass

-- | Re-parses every line of the current 'Proof'
proofReparse :: Effect ROOT Model Action
proofReparse = get >>= \m -> proof %= reparseProof m

-- | Re-parses a single 'Derivation' or 'Assumption'.
naReparseLine :: NodeAddr -> Effect ROOT Model Action
naReparseLine na =
  get >>= \m ->
    use proof >>= \p -> case (naLookup na p, fromNodeAddr na p) of
      (Just (Left (a, r)), Just lineNo) ->
        proof %=? naUpdateFormula (Left $ const (reparse m lineNo a, r)) na
      (Just (Right (Derivation f _)), Just lineNo) ->
        proof %=? naUpdateFormula (Right $ const (reparse m lineNo f)) na
      _ -> pass

-- | Move or create a 'Assumption', 'Derivation' or 'Proof' before a given 'NodeAddr'.
dropBeforeLine :: NodeAddr -> Effect ROOT Model Action
dropBeforeLine targetAddr = do
  m <- get
  use dragTarget >>= \case
    Nothing -> pass
    Just (Left na) -> do
      use proof >>= \p -> case naMoveBefore targetAddr na p of
        Nothing -> pass
        Just (ta, p) -> do
          proof %= const p
          naReparseLine ta
    Just (Right pa) -> do
      proof %=? \p -> do
        paTarget <- paFromNA targetAddr p
        snd <$> paMoveBefore paTarget pa p
  use spawnType >>= \case
    Nothing -> pass
    Just SpawnLine -> do
      use proof
        >>= \p ->
          case naInsertBefore
            (Right $ _get emptyDerivation m)
            targetAddr
            p of
            Just (na, p) -> do
              proof .= p
              setFocus (Left na)
            _ -> pass
    Just SpawnProof ->
      use proof
        >>= \p -> case join $
          liftA3
            paInsertBefore
            (pure $ SubProof [] [] (_get emptyDerivation m))
            (paFromNA targetAddr p)
            (pure p) of
          Just (pa, p) -> do
            proof .= p
            setFocus (Left $ naFromPA pa NAConclusion)
          _ -> pass
  clearDrag >> updateProof

{- | Set focus to a @<input>@ field specified by a 'NodeAddr'
(either the formula or the rule).
-}
setFocus :: Either NodeAddr NodeAddr -> Effect ROOT Model Action
setFocus ea = do
  focusedLine .= Just ea
  p <- use proof
  case ea of
    Left na -> io_ $ focus (mkFormulaInputId na p)
    Right na -> io_ $ focus (mkRuleInputId na p)

-- | Show the @<popover>@ with the given @id@.
showPopover :: MisoString -> IO ()
showPopover name = void $ getElementById name >>= \ref -> ref # "showPopover" $ ()

-- | Hide the @<popover>@ with the given @id@.
hidePopover :: MisoString -> IO ()
hidePopover name = void $ getElementById name >>= \ref -> ref # "hidePopover" $ ()

-- * Parsing

-- | Class for parsing `Text`
class FromText a where
  {- | Takes a `Model` and some `Text` and tries to parse it to the desired type.
  On failure returns an error message.
  -}
  fromText :: Model -> Int -> Text -> Either Text a

instance FromText RawFormula where
  fromText :: Model -> Int -> Text -> Either Text RawFormula
  fromText m = parseFormula (FormulaParserState (m ^. operators) (m ^. infixPreds) (m ^. quantifiers))

instance FromText RawAssumption where
  fromText :: Model -> Int -> Text -> Either Text RawAssumption
  fromText m =
    parseAssumption (FormulaParserState (m ^. operators) (m ^. infixPreds) (m ^. quantifiers))

instance FromText RuleApplication where
  fromText :: Model -> Int -> Text -> Either Text RuleApplication
  fromText _ = parseRuleApplication

{- | Wrapper for `fromText` that also takes a list of aliases and
tries to replace these aliases in the `Text`
-}
tryParse ::
  forall a.
  (FromText a) =>
  -- | The model.
  Model ->
  -- | Line number.
  Int ->
  -- | Text to parse.
  Text ->
  -- | Parse result.
  Wrapper a
tryParse m n txt = case fromText m n replacedTxt :: Either Text a of
  Left err -> Unparsed replacedTxt err
  Right result -> ParsedValid replacedTxt result
 where
  replacedTxt =
    foldr
      (\(alias, name) t -> T.replace alias name t)
      (foldr (\(alias, name, _) t -> T.replace alias name t) txt (m ^. operators))
      (m ^. quantifiers)

-- | Takes some 'Wrapper' and re-parses it.
reparse ::
  forall a.
  (FromText a) =>
  -- | The model.
  Model ->
  -- | The line number.
  Int ->
  -- | The wrapper to re-parse.
  Wrapper a ->
  -- | Parse result.
  Wrapper a
reparse m n w = tryParse m n (getText w)

-- | Uses 'reparse' to re-parse the whole 'Proof'.
reparseProof :: Model -> Proof -> Proof
reparseProof model = pMapLinesWithLineNo reparseAssumption reparseDerivation
 where
  reparseDerivation line (Derivation f r) = Derivation (reparse model line f) (reparse model line r)
  reparseAssumption line (a, r) = (reparse model line a, reparse model line r)
