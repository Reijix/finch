module App.Views where

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
import Relude.Extra (toPairs)
import Util (interleave)

-----------------------------------------------------------------------------

-- * Views

-----------------------------------------------------------------------------

-- | Takes a `Model` and returns the corresponding `View`.
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

viewNewProof :: Model -> View Model Action
viewNewProof model =
  H.button_
    [ HP.class_ "app-button"
    , onClick (SetProof (model ^. emptyProof))
    ]
    [text "New Proof"]

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
    , viewNewProof model
    ]

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
      [ viewUsageAccordion
      , viewGrammarAccordion model
      , viewRuleAccordion model
      , viewExamplesAccordion model
      ]

viewAccordion :: View Model Action -> View Model Action -> View Model Action
viewAccordion heading content =
  H.details_
    [HP.open_ True, HP.class_ "sidebar-element"]
    [ H.summary_
        [HP.class_ "sidebar-header"]
        [ heading
        , H.span_
            [HP.class_ "material-symbols-outlined", HP.class_ "summary-arrow"]
            ["keyboard_arrow_down"]
        ]
    , content
    ]

viewTextWithIcon :: MisoString -> MisoString -> View Model Action
viewTextWithIcon txt icon = H.div_ [HP.class_ "icon-text"] [viewMaterialIcon icon, text txt]

viewMaterialIcon :: MisoString -> View Model Action
viewMaterialIcon name = H.span_ [HP.class_ "material-symbols-outlined"] [text name]

viewProofActionsHeader :: View Model Action
viewProofActionsHeader =
  H.div_
    [HP.class_ "proof-actions-header"]
    [ viewSpawnNode SpawnLine "Drag over proof to add a line" "add" "Add Line"
    , viewBin
    , viewSpawnNode SpawnProof "Drag over proof to add a subproof" "variable_add" "Add Subproof"
    ]

viewProofActions :: View Model Action
viewProofActions =
  H.div_
    [ HP.class_ "sidebar-element"
    ]
    [ H.p_
        [HP.class_ "sidebar-header"]
        [viewTextWithIcon "Proof Actions" "action_key", H.span_ [] []]
    , H.div_
        [HP.class_ "row-sidebar-content"]
        [ viewBin
        , H.div_
            [HP.class_ "spawn-buttons"]
            [ viewSpawnNode SpawnLine "Drag over proof to add a line" "add" "Add Line"
            , viewSpawnNode SpawnProof "Drag over proof to add a subproof" "variable_add" "Add Subproof"
            ]
        ]
    ]

viewUsageAccordion :: View Model Action
viewUsageAccordion =
  viewAccordion
    (viewTextWithIcon "Usage Info" "info")
    ( H.ul_
        [HP.class_ "column-sidebar-content"]
        [ H.li_ [] ["Use the buttons at the top of the screen to add lines and subproofs."]
        , H.li_ [] ["Drag lines and subproofs to modify the proof."]
        , H.li_ [] ["Drag lines and subproofs to the trash can at the top to delete them."]
        , H.li_ [] ["Click lines to edit their contents."]
        , H.li_ [] ["Check below how to write the symbols and how the rules are defined."]
        ]
    )

viewGrammarAccordion :: Model -> View Model Action
viewGrammarAccordion model =
  viewAccordion
    (viewTextWithIcon "Symbols" "abc")
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

viewRuleAccordion :: Model -> View Model Action
viewRuleAccordion model =
  viewAccordion
    (viewTextWithIcon "Rules" "rule")
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

viewExamplesAccordion :: Model -> View Model Action
viewExamplesAccordion model =
  viewAccordion
    (viewTextWithIcon "Examples" "menu")
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

viewSpawnNode :: SpawnType -> MisoString -> MisoString -> MisoString -> View Model Action
viewSpawnNode tp title icon str =
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

viewErrorBox :: MisoString -> MisoString -> View Model Action
viewErrorBox name err =
  H.code_
    [ HP.class_ "tooltip"
    , HP.id_ name
    , textProp "popover" "manual"
    , HP.draggable_ False
    ]
    [text err]

mkFormulaInputId :: NodeAddr -> Proof -> MisoString
mkFormulaInputId na p = "formula-input-" <> show (lineNoOr999 na p)

mkRuleInputId :: NodeAddr -> Proof -> MisoString
mkRuleInputId na p = "rule-input-" <> show (lineNoOr999 na p)

viewLine :: Model -> NodeAddr -> Either Assumption Derivation -> View Model Action
viewLine model na e =
  let
    lineno = lineNoOr999 na (model ^. proof)
    errorBoxId = "formula-error-" <> show lineno
    inputId = mkFormulaInputId na (model ^. proof)
   in
    H.div_
      [ HP.class_ "formula-container"
      , HP.draggable_ ((model ^. focusedLine) /= Just (Left na))
      , if (model ^. focusedLine) /= Just (Left na)
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
              , ("draggable", Just (Left na) /= model ^. focusedLine)
              , ("focused", Just (Left na) == model ^. focusedLine)
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

viewLineNos :: Model -> View Model Action
viewLineNos model = H.div_ [HP.class_ "line-no-container"] $ one $ goProof 1 id (model ^. proof)
 where
  lineNoFor :: Int -> View Model Action
  lineNoFor = H.p_ [HP.class_ "line-no", HP.draggable_ False] . one . text . ms
  goProof :: Int -> (NodeAddr -> NodeAddr) -> Proof -> View Model Action
  goProof lineNo na (SubProof fs ps c) =
    H.div_
      [HP.class_ "line-no-wrapper", HP.draggable_ False]
      ( interleaveWithDropZones model (Just "empty-last-assumption") Nothing (na . NAAssumption) goFs
          <> interleaveWithDropZones model Nothing (Just (na NAConclusion)) (na . NALine) goPs
          <> drop 1 (interleaveWithDropZones model Nothing (Just (na NAAfterConclusion)) (const $ na NAAfterConclusion) (one goC))
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

viewRules :: Model -> View Model Action
viewRules model = H.div_ [HP.class_ "rules-container"] $ one $ go id (model ^. proof)
 where
  go :: (NodeAddr -> NodeAddr) -> Proof -> View Model Action
  go na (SubProof fs ps c) =
    H.div_
      [HP.class_ "rules-wrapper"]
      ( interleaveWithDropZones model (Just "empty-last-assumption") Nothing (na . NAAssumption) goFs
          <> interleaveWithDropZones model Nothing (Just (na NAConclusion)) (na . NALine) goPs
          <> drop 1 (interleaveWithDropZones model Nothing (Just (na NAAfterConclusion)) (const $ na NAAfterConclusion) (one goC))
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
                , ("focused", Just (Right na) == model ^. focusedLine)
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

-- TODO can use _viewProof with na = id
viewProof :: Model -> View Model Action
viewProof model =
  H.div_
    [ HP.class_ "proof-container-border"
    , onDragEnterWithOptions preventDefault DragLeave
    ]
    [ H.div_
        [HP.class_ "proof-container", onDragEnterWithOptions stopPropagation Nop]
        [viewLineNos model, proofView, viewRules model]
    ]
 where
  proofView =
    H.div_
      [HP.class_ "formulae-container"]
      ( interleaveWithDropZones model (Just "last-assumption") Nothing NAAssumption viewAssumptions
          <> interleaveWithDropZones model Nothing (Just NAConclusion) NALine viewProofs
          <> drop 1 (interleaveWithDropZones model Nothing (Just NAAfterConclusion) (const NAAfterConclusion) (one viewConclusion))
      )
   where
    (SubProof fs ps d) = model ^. proof
    viewAssumptions =
      snd $
        L.mapAccumL
          (\n f -> (n + 1, viewLine model (NAAssumption n) (Left f)))
          0
          fs
    viewProofs =
      snd $
        L.mapAccumL
          (\n e -> (n + 1, either (viewLine model (NALine n) . Right) (_viewProof (PAProof n) (NAProof n)) e))
          0
          ps
    viewConclusion = viewLine model NAConclusion (Right d)
  _viewProof :: ProofAddr -> (NodeAddr -> NodeAddr) -> Proof -> View Model Action
  _viewProof pa na (SubProof fs ps d) =
    H.div_
      [ HP.class_ "subproof"
      , HP.class_ "draggable"
      , HP.id_ (show pa)
      , HP.draggable_ True
      , onDragStartWithOptions stopPropagation $ DragStart (Right pa)
      , onDragEndWithOptions defaultOptions DragEnd
      ]
      ( interleaveWithDropZones model (Just "last-assumption") Nothing (na . NAAssumption) viewAssumptions
          <> interleaveWithDropZones model Nothing (Just (na NAConclusion)) (na . NALine) viewProofs
          <> drop 1 (interleaveWithDropZones model Nothing (Just (na NAAfterConclusion)) (const $ na NAAfterConclusion) (one viewConclusion))
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
                  (_viewProof (paProofToNested pa $ PAProof m) (na . NAProof m))
                  e
              )
          )
          0
          ps
    viewConclusion = viewLine model (na NAConclusion) (Right d)

-----------------------------------------------------------------------------

-- * Utilities

-----------------------------------------------------------------------------

viewDropZoneAt :: Model -> Maybe MisoString -> NodeAddr -> View Model Action
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

interleaveWithDropZones :: Model -> Maybe MisoString -> Maybe NodeAddr -> (Int -> NodeAddr) -> [View Model Action] -> [View Model Action]
interleaveWithDropZones model mclass lastNA na views = interleave dropzones views
 where
  dropzones :: [View Model Action]
  dropzones =
    map
      (\n -> viewDropZoneAt model (if n == length views then mclass else Nothing) (if n == length views then fromMaybe (na n) lastNA else na n))
      [0 .. length views]