{- |
Module      : App.Update
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

The update loop of the application, basically all of its logic.
-}
module App.Update where

------------------------------------------------------------------------------------------

import App.Model
import App.URLDecoder
import App.Views
import Data.Text qualified as T
import Fitch.Proof
import Fitch.Verification
import Miso (
  Effect,
  MisoString,
  ROOT,
  URI (..),
  back,
  castJSVal,
  consoleLog,
  focus,
  forward,
  fromMisoString,
  getElementById,
  getProperty,
  getURI,
  io,
  io_,
  jsNull,
  ms,
  prettyURI,
  pushURI,
  setSelectionRange,
  setSessionStorage,
  (!),
  (#),
 )
import Miso.DSL (jsg, (#))
import Miso.Effect (Sub)
import Miso.FFI.QQ (js)
import Miso.Html.Element qualified as H
import Miso.Html.Property qualified as HP
import Miso.Lens (Lens, LensCore (_get), use, (%=), (.=), (<~), (^.))
import Miso.Subscription.Util (createSub)
import Parser.Formula (
  FormulaParserState (FormulaParserState),
  parseAssumption,
  parseFormula,
 )
import Parser.Proof (parseProof)
import Parser.Rule (parseRuleApplication)
import Relude.Extra.Map (insert, member, (!?))
import Util ((%=?))

------------------------------------------------------------------------------------------

-- * Update loop

-- | Main execution loop of the application.
updateModel :: Action -> Effect ROOT Model Action
------------------------------------
-- Setup events
updateModel Setup = proofReparse >> checkProof >> updateTitle >> replaceInitialURI
updateModel (InitMathJAX domRef) = io_ [js| MathJax.typesetPromise([${domRef}]); |]
updateModel (SetProof p) =
  whenM (use proof <&> (/= p)) $ do
    proof .= p
    proofReparse
    updateProof
    whenM (use onMobile) toggleSidebar
updateModel (Resize b) = onMobile .= b
------------------------------------
-- t'URI' events
updateModel (PopState uri) = do
  readURI uri >> proofReparse >> checkProof >> updateTitle
updateModel NavigateForward = io_ forward
updateModel NavigateBackward = io_ back
------------------------------------
-- Events that toggle UI elements
updateModel (OpenTooltip name True) =
  use dragging >>= \case
    True -> pass
    False -> showTooltip name
updateModel (OpenTooltip _ False) = pass
updateModel CloseTooltip = hideTooltip
updateModel ToggleSidebar = toggleSidebar
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
      Just (canSpawnBefore na -> True) ->
        currentHoverLine .= Just na
      Just (canSpawnBefore na -> False) ->
        currentHoverLine .= Nothing
      Nothing ->
        use dragTarget >>= \case
          Just (Left (flip (naCanMoveBefore p) na -> True)) -> currentHoverLine .= Just na
          Just (Right sourcePA) -> case paFromNA na p of
            Nothing -> currentHoverLine .= Nothing
            Just targetPA ->
              currentHoverLine
                .= if paCanMoveBefore sourcePA targetPA then Just na else Nothing
          _ -> currentHoverLine .= Nothing
updateModel DragLeave = currentHoverLine .= Nothing
updateModel (SpawnStart st) = do
  hideTooltip
  dragging .= True
  spawnType .= Just st
updateModel (DragStart dt) = do
  hideTooltip
  dragging .= True
  lastDragged .= Nothing
  dragTarget .= Just dt
updateModel DragEnd = do
  chl <- use currentHoverLine
  whenJust chl dropBeforeLine
  clearDrag
------------------------------------
-- Input related events
updateModel (Focus ea) = do
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

------------------------------------------------------------------------------------------

-- * Effects

{- | Re-checks a t'Proof', i.e. runs the verifier, updates the t'URI' and document title.

Should be called after every change to the t'Proof'.
-}
updateProof :: Effect ROOT Model Action
updateProof = checkProof >> pushProofURI >> updateTitle

{- | Updates the @document.title@ to show how many errors there are and
what the conclusion of the t'Proof' is.
-}
updateTitle :: Effect ROOT Model Action
updateTitle = do
  p@(SubProof _ _ (Derivation f _)) <- use proof
  let title =
        ( case proofErrors p of
            0 -> mempty
            n -> show n <> " ✖ | "
        )
          <> prettyPrint f
  io_ [js| document.title = ${title} |]

{- | Runs the t'Proof' verification algorithm, i.e.

1. Checks that symbols only occur with the same arity
2. Checks freshness t'Assumption's
3. Verifies all t'RuleApplication's.
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

-- | Takes a t'URI' and reads in a proof if it contains one.
readURI :: URI -> Effect ROOT Model Action
readURI uri = do
  case uriQueryString uri !? "proof" of
    Just (Just str) -> case decodeFromUrl (fromMisoString str :: Text) of
      Nothing -> pass
      Just (p :: Proof) -> proof .= p
    _ -> pass

{- | Pushes a new t'URI' that has the t'Proof' encoded to the history stack.

See @static/Navigation.js@ for the used @pushStateHistory@ function.
-}
pushProofURI :: Effect ROOT Model Action
pushProofURI = do
  p <- use proof
  io_ $ do
    uri <- getURI
    let newURI =
          uri
            { uriQueryString =
                insert "proof" (Just . ms $ encodeForUrl p) (uriQueryString uri)
            }
    if uri /= newURI
      then void $ jsg "window" # "pushStateHistory" $ prettyURI newURI
      else pass

{- | To be called in the v'Setup' t'Action'.
Replaces the initial URI that possible does not contain the queryParameters,
with a URI that does. Also initializes the tracking of the HTML5 historu API.

See @static/Navigation.js@ for the used @initHistory@ function.
-}
replaceInitialURI :: Effect ROOT Model Action
replaceInitialURI = do
  p <- use proof
  l <- use logic
  io_ $ do
    uri <- getURI
    let newURI =
          URI
            { uriPath = uriPath uri
            , uriQueryString =
                one ("proof", Just . ms $ encodeForUrl p)
                  <> one ("logic", Just $ show l)
            , uriFragment = ""
            }
    void $ jsg "window" # "initHistory" $ prettyURI newURI

-- | Re-parses every line of the current t'Proof'
proofReparse :: Effect ROOT Model Action
proofReparse = get >>= \m -> proof %= reparseProof m

-- | Re-parses a single t'Derivation' or t'Assumption'.
naReparseLine :: NodeAddr -> Effect ROOT Model Action
naReparseLine na =
  get >>= \m ->
    use proof >>= \p -> case (naLookup na p, fromNodeAddr na p) of
      (Just (Left (a, r)), Just lineNo) ->
        proof %=? naUpdateFormula (Left $ const (reparse m lineNo a, r)) na
      (Just (Right (Derivation f _)), Just lineNo) ->
        proof %=? naUpdateFormula (Right $ const (reparse m lineNo f)) na
      _ -> pass

-- | Move or create a t'Assumption', t'Derivation' or t'Proof' before a given t'NodeAddr'.
dropBeforeLine :: NodeAddr -> Effect ROOT Model Action
dropBeforeLine targetAddr = do
  m <- get
  p <- use proof
  use dragTarget >>= \case
    Nothing -> pass
    Just (Left na) -> do
      use proof >>= \p -> case naMoveBefore targetAddr na p of
        Nothing -> lastDragged .= Just na
        Just (ta, p) -> do
          proof %= const p
          naReparseLine ta
    Just (Right pa) -> do
      p <- use proof
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
            Just (na, p) -> proof .= p
            _ -> pass
    Just SpawnProof ->
      use proof
        >>= \p -> case join $
          liftA3
            paInsertBefore
            (pure $ SubProof [] [] (_get emptyDerivation m))
            (paFromNA targetAddr p)
            (pure p) of
          Just (pa, p) -> proof .= p
          _ -> pass
  clearDrag >> updateProof

{- | Set focus to a @<input>@ field specified by a t'NodeAddr'
(either the t'Formula' or the t'RuleApplication').
-}
setFocus :: Either NodeAddr NodeAddr -> Effect ROOT Model Action
setFocus ea = do
  focusedLine .= Just ea
  p <- use proof
  case ea of
    Left na -> io_ $ focus (mkFormulaInputId na p)
    Right na -> io_ $ focus (mkRuleInputId na p)

-- | Show the @<popover>@ with the given @id@.
showTooltip :: MisoString -> Effect ROOT Model Action
showTooltip name = do
  tt <- use currentTooltip
  if tt == Just name
    then pass
    else do
      io_ [js| let ref = document.getElementById(${name}); if (ref) { ref.showPopover() } |]
      currentTooltip .= Just name

-- | Hide the @<popover>@ with the given @id@.
hideTooltip :: Effect ROOT Model Action
hideTooltip = do
  tt <- use currentTooltip
  case tt of
    Nothing -> pass
    Just name -> do
      io_ [js| let ref = document.getElementById(${name}); if (ref) { ref.hidePopover() } |]
      currentTooltip .= Nothing

-- | Flip the sidebar state and save it in sessionStorage
toggleSidebar :: Effect ROOT Model Action
toggleSidebar = do
  sidebarToggle %= not
  st <- use sidebarToggle
  io_ $ setSessionStorage "sidebarToggle" (ms $ show st)

-- * Parsing

-- | Class for parsing t`Text`
class FromText a where
  {- | Takes a t`Model` and some t`Text` and tries to parse it to the desired type.
  On failure returns an error message.
  -}
  fromText :: Model -> Int -> Text -> Either Text a

instance FromText RawFormula where
  fromText :: Model -> Int -> Text -> Either Text RawFormula
  fromText m =
    parseFormula
      ( FormulaParserState
          (m ^. operators)
          (m ^. infixPreds)
          (m ^. quantifiers)
      )

instance FromText RawAssumption where
  fromText :: Model -> Int -> Text -> Either Text RawAssumption
  fromText m =
    parseAssumption
      ( FormulaParserState
          (m ^. operators)
          (m ^. infixPreds)
          (m ^. quantifiers)
      )

instance FromText RuleApplication where
  fromText :: Model -> Int -> Text -> Either Text RuleApplication
  fromText _ = parseRuleApplication

{- | Wrapper for `fromText` that also takes a list of aliases and
tries to replace these aliases in the t`Text`
-}
tryParse ::
  forall a.
  (FromText a) =>
  -- | The t'Model'.
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

-- | Takes some t'Wrapper' and re-parses it.
reparse ::
  forall a.
  (FromText a) =>
  -- | The t'Model'.
  Model ->
  -- | The line number.
  Int ->
  -- | The t'Wrapper' to re-parse.
  Wrapper a ->
  -- | Parse result.
  Wrapper a
reparse m n w = tryParse m n (getText w)

-- | Uses 'reparse' to re-parse the whole t'Proof'.
reparseProof :: Model -> Proof -> Proof
reparseProof model = pMapLinesWithLineNo reparseAssumption reparseDerivation
 where
  reparseDerivation line (Derivation f r) =
    Derivation
      (reparse model line f)
      (reparse model line r)
  reparseAssumption line (a, r) =
    (reparse model line a, reparse model line r)
