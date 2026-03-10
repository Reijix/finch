{- |
Module      : App.Views
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (GHCJS)

This module defines the Miso t'View's of the application.
-}
module App.Views where

-----------------------------------------------------------------------------
import App.Model
import Data.Either (isLeft)
import Data.List qualified as L
import Fitch.Proof
import Miso (
  Attribute,
  MisoString,
  Phase (BUBBLE),
  PointerEvent,
  View,
  defaultOptions,
  emptyDecoder,
  focus,
  fromMisoString,
  keyInfoDecoder,
  ms,
  onBeforeDestroyed,
  onCreatedWith,
  onWithOptions,
  optionalAttrs,
  pointerDecoder,
  preventDefault,
  stopPropagation,
  text,
  textRaw,
  valueDecoder,
 )
import Miso qualified as HP
import Miso.CSS (styleInline_)
import Miso.Html.Element qualified as H
import Miso.Html.Event
import Miso.Html.Property (value_)
import Miso.Html.Property qualified as HP
import Miso.Lens
import Miso.Property (boolProp, textProp)
import Miso.Router (URI (..), prettyURI)
import Relude.Extra (toPairs)
import Relude.Unsafe (fromJust)
import Util (interleave)

-----------------------------------------------------------------------------

-- * Views

{- | Takes a 'Model' and returns the corresponding 'View'
containing a sidebar, the proof workspace and a header.
-}
viewModel :: Model -> View Model Action
viewModel model =
  H.div_
    [HP.class_ "app-container"]
    [ viewHeader model
    , H.div_
        [HP.class_ "content-container"]
        [ viewSidebar model
        , viewProof model
        ]
    ]

-----------------------------------------------------------------------------

-- ** Header

-- | Returns the header of the application.
viewHeader :: Model -> View Model Action
viewHeader model =
  H.header_
    [HP.class_ "header"]
    [ H.h1_
        []
        [ H.img_ [HP.src_ "favicon.svg"]
        , "Finch"
        , H.button_ [HP.class_ "help-button", onClick ToggleSidebar] [viewMaterialIcon "help"]
        ]
    , viewProofActionsHeader
    , viewNewProofButton model
    ]

{- | For use in 'viewHeader',
returns buttons for spawning lines/subproofs and a trash can.
-}
viewProofActionsHeader :: View Model Action
viewProofActionsHeader =
  H.div_
    [HP.class_ "proof-actions-header"]
    [ viewSpawnNode SpawnLine "Drag over proof to add a line" "add"
    , viewBin
    , viewSpawnNode SpawnProof "Drag over proof to add a subproof" "variable_add"
    ]

{- | For use in 'viewProofActionsHeader',
returns a trash can, where elements can be deleted.
-}
viewBin :: View Model Action
viewBin =
  H.div_
    [ onDragOverWithOptions preventDefault Nop
    , onDragEnterWithOptions preventDefault Nop
    , onDragLeaveWithOptions preventDefault Nop
    , onDropWithOptions defaultOptions (Drop LocationBin)
    , HP.class_ "bin"
    , HP.class_ "icon-container"
    , HP.title_ "Drag lines or subproofs here to delete them."
    ]
    [ viewMaterialIcon "delete"
    ]

{- | For use in 'viewProofActionsHeader',
returns a button for spawning a node.
-}
viewSpawnNode ::
  -- | Type of node to be spawned.
  SpawnType ->
  -- | Tooltip of the button
  MisoString ->
  -- | The buttons icon.
  MisoString ->
  View Model Action
viewSpawnNode tp title icon =
  H.div_
    [ HP.class_ "spawn-button"
    , HP.class_ "draggable"
    , HP.draggable_ True
    , HP.title_ title
    , onDragStartWithOptions stopPropagation $ SpawnStart tp
    , onDragEndWithOptions defaultOptions DragEnd
    , HP.class_ "icon-container"
    ]
    [ viewMaterialIcon icon
    ]

{- | For use in 'viewHeader',
returns a button for starting a new proof.
-}
viewNewProofButton :: Model -> View Model Action
viewNewProofButton model =
  H.button_
    [ HP.class_ "app-button"
    , onClick (SetProof (model ^. emptyProof))
    ]
    [text "New Proof"]

-----------------------------------------------------------------------------

-- ** Sidebar

-- | Returns the sidebar of the application
viewSidebar :: Model -> View Model Action
viewSidebar model =
  H.div_
    [ HP.class_ "sidebar"
    , onDragEnterWithOptions (preventDefault <> stopPropagation) DragLeave
    , HP.classList_
        [ ("sidebar-open", model ^. sidebarToggle)
        , ("sidebar-closed", not (model ^. sidebarToggle))
        ]
    ]
    $ one
    $ H.div_
      [ HP.class_ "sidebar-content"
      ]
      [ viewUsage
      , viewGrammar model
      , viewRules model
      , viewExamples model
      , viewLogics model
      ]

-- | Wrapper for creating @<details>@ elements in the sidebar.
viewDetails ::
  -- | Text of the <details> summary.
  MisoString ->
  -- | Icon of the <details> summary.
  MisoString ->
  -- | Content of the <details> element.
  View Model Action ->
  View Model Action
viewDetails txt icon content =
  H.details_
    [HP.open_ True, HP.class_ "sidebar-element"]
    [ H.summary_
        [HP.class_ "sidebar-header"]
        [ H.div_ [HP.class_ "icon-text"] [viewMaterialIcon icon, text txt]
        , H.span_
            [HP.class_ "material-symbols-outlined", HP.class_ "summary-arrow"]
            ["keyboard_arrow_down"]
        ]
    , content
    ]

{- | For use in 'viewSidebar',
returns usage instructions.
-}
viewUsage :: View Model Action
viewUsage =
  viewDetails
    "Usage Info"
    "info"
    ( H.ul_
        [HP.class_ "column-sidebar-content"]
        [ H.li_ [] ["Use the buttons at the top of the screen to add lines and subproofs."]
        , H.li_ [] ["Drag lines and subproofs to modify the proof."]
        , H.li_ [] ["Drag lines and subproofs to the trash can at the top to delete them."]
        , H.li_ [] ["Click lines to edit their contents."]
        , H.li_ [] ["Check below how to write the symbols and how the rules are defined."]
        ]
    )

{- | For use in 'viewSidebar',
returns a list of buttons that enable the user to change the underlying logic of the proof checker.
-}
viewLogics :: Model -> View Model Action
viewLogics model =
  viewDetails
    "Logics"
    "schema"
    ( H.div_
        [HP.class_ "column-sidebar-content"]
        (map mkLogic [("First-order logic", "fol"), ("Propositional Logic", "prop")])
    )
 where
  mkLogic :: (Text, MisoString) -> View Model Action
  mkLogic (name, alias) =
    H.a_
      [ HP.class_ "app-button"
      , HP.class_ "example-button"
      , HP.href_ $
          prettyURI $
            URI
              { uriPath = uriPath (model ^. uri)
              , uriFragment = ""
              , uriQueryString = one ("logic", Just alias)
              }
      ]
      [text $ ms name]

{- | For use in 'viewSidebar',
returns a list of symbols that can be used, and on hover shows their aliases.
-}
viewGrammar :: Model -> View Model Action
viewGrammar model =
  viewDetails
    "Symbols"
    "function"
    ( H.div_
        [HP.class_ "row-sidebar-content"]
        ( map
            viewSingleSymbol
            ( map (\(a, b, _) -> (a, b)) (model ^. operators)
                <> model ^. quantifiers
                <> model ^. infixPreds
            )
        )
    )
 where
  viewSingleSymbol :: (Name, Name) -> View Model Action
  viewSingleSymbol ("", symbol) =
    H.button_
      [ HP.class_ "app-button"
      , HP.class_ "symbol-button"
      ]
      [text $ ms symbol]
  viewSingleSymbol (alias, symbol) =
    H.div_
      [HP.class_ "anchor-container"]
      [ H.button_
          [ HP.class_ "app-button"
          , HP.class_ "anchor"
          , HP.class_ "symbol-button"
          , onMouseOver (PopOpen (ms alias) True)
          , onMouseOut (PopClose (ms alias))
          ]
          [text $ ms symbol]
      , H.p_
          [ HP.class_ "tooltip"
          , HP.class_ "anchored"
          , HP.id_ (ms alias)
          , textProp "popover" "manual"
          , HP.draggable_ False
          ]
          [text . ms $ "Alias: " <> alias]
      ]

{- | For use in 'viewSidebar',
returns a list of the logics' rules, on hover shows the rule definition.
-}
viewRules :: Model -> View Model Action
viewRules model =
  viewDetails
    "Rules"
    "rule"
    (H.div_ [HP.class_ "row-sidebar-content"] (map viewSingleRule (toPairs $ model ^. rules)))
 where
  viewSingleRule :: (Name, RuleSpec) -> View Model Action
  viewSingleRule (name, rs) =
    H.div_
      [HP.class_ "anchor-container", HP.class_ "rulebox-container"]
      [ H.button_
          [ HP.class_ "app-button"
          , HP.class_ "anchor"
          , HP.class_ "rule-button"
          , onMouseOver (PopOpen (ms name) True)
          , onMouseOut (PopClose (ms name))
          ]
          [text $ ms name]
      , H.p_
          [ HP.class_ "tooltip"
          , HP.class_ "anchored"
          , HP.id_ (ms name)
          , onCreatedWith InitMathJAX
          , textProp "popover" "manual"
          , HP.draggable_ False
          ]
          [text . ms $ "\\[(\\mathrm{" <> name <> "})" <> ruleSpecTex rs <> "\\]"]
      ]

{- | For use in 'viewSidebar',
returns a list of example proofs, on hover shows the assumptions and conclusion of the proof.
-}
viewExamples :: Model -> View Model Action
viewExamples model =
  viewDetails
    "Examples"
    "menu"
    (H.div_ [HP.class_ "column-sidebar-content"] (map mkExample (model ^. exampleProofs)))
 where
  mkExample :: (Text, Proof) -> View Model Action
  mkExample (name, p) =
    H.div_
      [HP.class_ "anchor-container", HP.class_ "example-container"]
      [ H.button_
          [ HP.class_ "app-button"
          , HP.class_ "anchor"
          , HP.class_ "example-button"
          , onMouseOver (PopOpen (ms name) True)
          , onMouseOut (PopClose (ms name))
          , onClick (SetProof p)
          ]
          [text $ ms name]
      , H.p_
          [ HP.class_ "tooltip"
          , HP.class_ "anchored"
          , HP.id_ (ms name)
          , onCreatedWith InitMathJAX
          , textProp "popover" "manual"
          , HP.draggable_ False
          ]
          [text . ms $ proofPreviewTex p]
      ]

-----------------------------------------------------------------------------

-- ** Proof

{- | Shows the proof workspace of the application, containing a list of linenumbers,
a list of formula inputs and a list of rule inputs.
-}
viewProof :: Model -> View Model Action
viewProof model =
  H.div_
    [ HP.class_ "proof-container-border"
    , onDragEnterWithOptions preventDefault DragLeave
    ]
    [ H.div_
        [HP.class_ "proof-container", onDragEnterWithOptions stopPropagation Nop]
        [viewLineNos model, proofView, viewRuleApplications model]
    ]
 where
  proofView =
    H.div_
      [HP.class_ "formulae-container"]
      [_viewProof Nothing id (model ^. proof)]
  _viewProof :: Maybe ProofAddr -> (NodeAddr -> NodeAddr) -> Proof -> View Model Action
  _viewProof pa na (SubProof fs ps d) =
    optionalAttrs
      H.div_
      [ HP.class_ "subproof"
      , HP.id_ (show pa)
      ]
      (isJust pa)
      [ HP.class_ "draggable"
      , HP.draggable_ (isNothing (model ^. focusedLine))
      , HP.classList_ [("drag-target", (Right <$> pa) == model ^. dragTarget)]
      , onDragStartWithOptions stopPropagation $ DragStart (Right (fromJust pa))
      , onDragEndWithOptions defaultOptions DragEnd
      ]
      ( interleaveWithDropZones
          model
          (Just "last-assumption")
          Nothing
          (na . NAAssumption)
          viewAssumptions
          <> interleaveWithDropZones model Nothing (Just (na NAConclusion)) (na . NALine) viewProofs
          <> drop
            1
            ( interleaveWithDropZones
                model
                Nothing
                (Just (na NAAfterConclusion))
                (const $ na NAAfterConclusion)
                (one viewConclusion)
            )
      )
   where
    viewAssumptions =
      snd $
        L.mapAccumL
          ( \m f ->
              ( m + 1
              , viewLine
                  model
                  (na (NAAssumption m))
                  (Left f)
              )
          )
          0
          fs
    viewProofs =
      snd $
        L.mapAccumL
          ( \m e ->
              ( m + 1
              , either
                  (viewLine model (na $ NALine m) . Right)
                  (_viewProof (maybe id paProofToNested pa <$> Just (PAProof m)) (na . NAProof m))
                  e
              )
          )
          0
          ps
    viewConclusion = viewLine model (na NAConclusion) (Right d)

{- | For use in 'viewProof',
returns a list of linenumbers that are shown to the left of the proof.
-}
viewLineNos :: Model -> View Model Action
viewLineNos model = H.div_ [HP.class_ "line-no-container"] $ one $ goProof 1 id (model ^. proof)
 where
  lineNoFor :: Int -> View Model Action
  lineNoFor = H.p_ [HP.class_ "line-no", HP.draggable_ False] . one . text . ms
  goProof :: Int -> (NodeAddr -> NodeAddr) -> Proof -> View Model Action
  goProof lineNo na (SubProof fs ps c) =
    H.div_
      [HP.class_ "line-no-wrapper", HP.draggable_ False]
      ( interleaveWithDropZones
          model
          (Just "empty-last-assumption")
          Nothing
          (na . NAAssumption)
          goFs
          <> interleaveWithDropZones model Nothing (Just (na NAConclusion)) (na . NALine) goPs
          <> drop
            1
            ( interleaveWithDropZones
                model
                Nothing
                (Just (na NAAfterConclusion))
                (const $ na NAAfterConclusion)
                (one goC)
            )
      )
   where
    ((lineNo', _), goFs) =
      mapAccumL (\(lineNo, d) f -> ((lineNo + 1, d + 1), lineNoFor lineNo)) (lineNo, 0) fs
    ((lineNo'', _), goPs) =
      mapAccumL
        ( \(lineNo, n) e ->
            either
              (\d -> ((lineNo + 1, n + 1), goDerivation lineNo (na $ NALine n) d))
              (\p -> ((lineNo + pLength p, n + 1), goProof lineNo (na . NAProof n) p))
              e
        )
        (lineNo', 0)
        ps
    goC = goDerivation lineNo'' (na NAConclusion) c
  goDerivation :: Int -> NodeAddr -> Derivation -> View Model Action
  goDerivation lineNo _ _ = lineNoFor lineNo

{- | For use in 'viewProof',
returns a list of 'RuleApplication's (judgements),
that are shown to the right of the proof.
-}
viewRuleApplications :: Model -> View Model Action
viewRuleApplications model = H.div_ [HP.class_ "rules-container"] $ one $ go id (model ^. proof)
 where
  go :: (NodeAddr -> NodeAddr) -> Proof -> View Model Action
  go na (SubProof fs ps c) =
    H.div_
      [HP.class_ "rules-wrapper"]
      ( interleaveWithDropZones
          model
          (Just "empty-last-assumption")
          Nothing
          (na . NAAssumption)
          goFs
          <> interleaveWithDropZones model Nothing (Just (na NAConclusion)) (na . NALine) goPs
          <> drop
            1
            ( interleaveWithDropZones
                model
                Nothing
                (Just (na NAAfterConclusion))
                (const $ na NAAfterConclusion)
                (one goC)
            )
      )
   where
    goFs = map (const $ H.p_ [HP.class_ "empty-rule"] [textRaw "\160"]) fs
    goPs =
      snd $
        mapAccumL
          (\n e -> (n + 1, either (goDerivation (na $ NALine n)) (go (na . NAProof n)) e))
          0
          ps
    goC = goDerivation (na NAConclusion) c
  goDerivation :: NodeAddr -> Derivation -> View Model Action
  goDerivation na (Derivation _ p) =
    let
      lineno = lineNoOr999 na (model ^. proof)
      inputId = mkRuleInputId na (model ^. proof)
      errorBoxId = "rule-error-" <> show lineno
     in
      H.div_
        [ onMouseOver (PopOpen errorBoxId hasError)
        , onMouseOut (PopClose errorBoxId)
        , HP.class_ "rule-container"
        , onClick $ FocusInput (Right na)
        ]
        [ viewErrorBox errorBoxId err
        , H.input_
            [ HP.class_ "rule-input"
            , HP.id_ inputId
            , HP.classList_
                [ ("has-error", hasError)
                ]
            , HP.autocomplete_ False
            , HP.draggable_ False
            , HP.inert_ (Just (Right na) /= model ^. focusedLine)
            , onBlur (Blur (Right na))
            , onWithOptions BUBBLE defaultOptions "input" valueDecoder Input
            , onChange (const Change)
            , onDragStartWithOptions preventDefault Nop
            , value_ ruleTxt
            ]
        ]
   where
    (hasError, ruleTxt, err) = case p of
      (ParsedValid str _) -> (False, ms str, "")
      (ParsedInvalid str err _) -> (True, ms str, ms err)
      (Unparsed str err) -> (True, ms str, ms err)

{- | Returns a errorbox that is shown on hover, containing proof errors
written in a @<code>@ element to get monospacing.
-}
viewErrorBox ::
  -- | @id@ of the errorbox.
  MisoString ->
  -- | Error message.
  MisoString ->
  View Model Action
viewErrorBox name err =
  H.code_
    [ HP.class_ "tooltip"
    , HP.id_ name
    , textProp "popover" "manual"
    , HP.draggable_ False
    ]
    [text err]

-- | Helper for turning a 'NodeAddr' to a formula inputfield id.
mkFormulaInputId :: NodeAddr -> Proof -> MisoString
mkFormulaInputId na p = "formula-input-" <> show (lineNoOr999 na p)

-- | Helper for turning a 'NodeAddr' to a rule inputfield id.
mkRuleInputId :: NodeAddr -> Proof -> MisoString
mkRuleInputId na p = "rule-input-" <> show (lineNoOr999 na p)

{- | For use in 'viewProof', shows a single line of the proof,
specified by its 'NodeAddr'.
-}
viewLine :: Model -> NodeAddr -> Either Assumption Derivation -> View Model Action
viewLine model na e =
  let
    lineno = lineNoOr999 na (model ^. proof)
    errorBoxId = "formula-error-" <> show lineno
    inputId = mkFormulaInputId na (model ^. proof)
   in
    H.div_
      [ HP.class_ "formula-container"
      , HP.class_ "draggable"
      , HP.draggable_ (isNothing (model ^. focusedLine))
      , if model ^. focusedLine /= Just (Left na)
          then onDragStartWithOptions stopPropagation $ DragStart (Left na)
          else onDragStartWithOptions (stopPropagation <> preventDefault) Nop
      , onDragEndWithOptions defaultOptions DragEnd
      , onMouseOver (PopOpen errorBoxId hasError)
      , onMouseOut (PopClose errorBoxId)
      , onClick $ FocusInput (Left na)
      ]
      [ H.input_
          [ HP.inert_ (Just (Left na) /= model ^. focusedLine)
          , HP.id_ inputId
          , HP.classList_
              [ ("formula-input", True)
              , ("has-error", hasError)
              , ("drag-target", Just (Left na) == model ^. dragTarget)
              , ("draggable", Just (Left na) /= model ^. focusedLine)
              ]
          , HP.autocomplete_ False
          , HP.draggable_ False
          , onBlur (Blur (Left na))
          , onChange (const Change)
          , onWithOptions BUBBLE defaultOptions "input" valueDecoder Input
          , onDragStartWithOptions preventDefault Nop
          , value_ txt
          ]
      , viewErrorBox errorBoxId err
      ]
 where
  (hasError, txt, err) = case e of
    Left (a, _) -> case a of
      ParsedValid str a' -> (False, ms str, "")
      ParsedInvalid str err a' -> (True, ms str, ms err)
      Unparsed str err -> (True, ms str, ms err)
    Right (Derivation f r) -> case f of
      (ParsedValid str f') -> (False, ms str, "")
      (ParsedInvalid str err f') -> (True, ms str, ms err)
      (Unparsed str err) -> (True, ms str, ms err)

-----------------------------------------------------------------------------

-- * Utilities

{- | Helper for viewing material icons based on their name,
see <https://fonts.google.com/icons>
-}
viewMaterialIcon :: MisoString -> View Model Action
viewMaterialIcon name = H.span_ [HP.class_ "material-symbols-outlined"] [text name]

{- |
Shows a dropzone for the given 'NodeAddr', i.e. a small empty div, where nodes can be dropped.

Expands, if a node can be dropped inside.
-}
viewDropZoneAt ::
  -- | The model.
  Model ->
  -- | Optional class for the dropzone.
  Maybe MisoString ->
  -- | The corresponding 'NodeAddr'.
  NodeAddr ->
  View Model Action
viewDropZoneAt model mclass na =
  H.div_
    [ HP.class_ "drop-zone"
    , HP.id_ (show na)
    , HP.classList_
        [ ("expanded-drop-zone", model ^. currentHoverLine == Just na)
        , (fromMaybe "" mclass, isJust mclass)
        , ("draggable", isJust mclass && not (isNAAssumption na))
        ]
    , HP.draggable_ (isNothing mclass) -- true to overshadow the draggable of subproof
    , onDragStartWithOptions (preventDefault <> stopPropagation) Nop
    , onDragOverWithOptions preventDefault Nop
    , onDragEnterWithOptions preventDefault (DragEnter na)
    , onDropWithOptions defaultOptions (Drop (LineAddr na))
    ]
    []

-- | Interleaves the list @views@ with dropzones of the corresponding @na@.
interleaveWithDropZones ::
  -- | The model.
  Model ->
  -- | Optionally a class for the last dropzone.
  Maybe MisoString ->
  -- | Optionally a differing 'NodeAddr' for the last dropzone.
  Maybe NodeAddr ->
  -- | A function for generating 'NodeAddr' from a number (e.g. turn @n@ into @'NAAssumption' n@).
  (Int -> NodeAddr) ->
  -- | The list of views to be interleaved.
  [View Model Action] ->
  [View Model Action]
interleaveWithDropZones model mclass lastNA na views = interleave dropzones views
 where
  dropzones :: [View Model Action]
  dropzones =
    map
      ( \n ->
          viewDropZoneAt
            model
            (if n == length views then mclass else Nothing)
            (if n == length views then fromMaybe (na n) lastNA else na n)
      )
      [0 .. length views]

-----------------------------------------------------------------------------
