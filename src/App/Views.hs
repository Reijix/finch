{- |
Module      : App.Views
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module defines the Miso t'View's of the application.
-}
module App.Views where

------------------------------------------------------------------------------------------
import App.Model
import Data.List qualified as L
import Fitch.Proof
import Miso (
  MisoString,
  Phase (BUBBLE),
  URI (..),
  View,
  defaultOptions,
  ms,
  onCreatedWith,
  onWithOptions,
  optionalAttrs,
  prettyURI,
  preventDefault,
  stopPropagation,
  text,
  textProp,
  textRaw,
  valueDecoder,
 )
import Miso.Html.Element qualified as H
import Miso.Html.Event qualified as HE
import Miso.Html.Property qualified as HP
import Miso.Lens ((^.))
import Miso.Property (textProp)
import Miso.Router (URI (..), prettyURI)
import Relude.Extra (toPairs)
import Relude.Unsafe (fromJust)
import Specification.Types
import Util (interleave)

------------------------------------------------------------------------------------------

-- * Views

{- | Takes a t'Model' and returns the corresponding t'View'
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

------------------------------------------------------------------------------------------

-- ** Header

-- | Returns the header of the application.
viewHeader :: Model -> View Model Action
viewHeader model =
  H.header_
    [HP.class_ "header"]
    [ viewLogoHeader
    , viewProofActionsHeader
    , viewNavigationButtons
    ]

-- | Shows the logo in the 'viewHeader', together with a title and navigation buttons
viewLogoHeader :: View Model Action
viewLogoHeader =
  H.div_
    [HP.class_ "logo-header"]
    [ viewMenuButton
    , H.img_ [HP.src_ "favicon.svg"]
    , H.h1_ [] ["Finch"]
    ]

-- | Adds navigation @<button>@s for accessing the browsers history API.
viewNavigationButtons :: View Model Action
viewNavigationButtons =
  H.div_
    [HP.class_ "navigation-container"]
    [ H.button_
        [ HE.onClick NavigateBackward
        , HP.class_ "navigation-button"
        , HP.id_ "back-button"
        ]
        [viewMaterialIcon "arrow_left_alt"]
    , H.button_
        [ HE.onClick NavigateForward
        , HP.class_ "navigation-button"
        , HP.id_ "forward-button"
        ]
        [viewMaterialIcon "arrow_right_alt"]
    ]

{- | For use in 'viewHeader',
returns buttons for spawning t'Assumption', t'Derivation', t'Proof' or a trash can.
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
    [ HE.onDragOverWithOptions preventDefault Nop
    , HE.onDragEnterWithOptions preventDefault Nop
    , HE.onDragLeaveWithOptions preventDefault Nop
    , HP.class_ "tooltip-container"
    , HP.class_ "tooltip-anchor"
    , HE.onMouseOver (PopOpen "bin" True)
    , HE.onMouseOut (PopClose "bin")
    , HE.onDropWithOptions defaultOptions (Drop LocationBin)
    , HP.class_ "bin"
    ]
    [ viewMaterialIcon "delete"
    , H.p_
        [ HP.class_ "tooltip-bottom"
        , HP.id_ "bin"
        , textProp "popover" "manual"
        , HP.draggable_ False
        ]
        [text "Drag lines or subproofs here to delete them."]
    ]

{- | For use in 'viewProofActionsHeader',
returns a button for spawning a t'Assumption', t'Derivation' or t'Proof'.
-}
viewSpawnNode ::
  -- | Type of node to be spawned
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
    , HP.class_ "tooltip-container"
    , HP.draggable_ True
    , HP.class_ "tooltip-anchor"
    , HE.onMouseOver (PopOpen (ms $ show tp) True)
    , HE.onMouseOut (PopClose (ms $ show tp))
    , HE.onDragStartWithOptions stopPropagation $ SpawnStart tp
    , HE.onDragEndWithOptions defaultOptions DragEnd
    ]
    [ viewMaterialIcon icon
    , H.p_
        [ HP.class_ "tooltip-bottom"
        , HP.id_ (show tp)
        , textProp "popover" "manual"
        , HP.draggable_ False
        ]
        [text title]
    ]

viewMenuButton :: View Model Action
viewMenuButton =
  H.button_
    [HE.onClick ToggleSidebar, HP.class_ "menu-button"]
    [viewMaterialIcon "menu"]

{- | For use in 'viewHeader',
returns a @<button>@ for starting a new t'Proof'.
-}
viewNewProofButton :: Model -> View Model Action
viewNewProofButton model =
  H.button_
    [ HP.class_ "new-proof-button"
    , HP.class_ "sidebar-element"
    , HE.onClick (SetProof $ SubProof [] [] (model ^. emptyDerivation))
    ]
    [text "Start New Proof"]

------------------------------------------------------------------------------------------

-- ** Sidebar

-- | Returns the sidebar of the application.
viewSidebar :: Model -> View Model Action
viewSidebar model =
  H.div_
    [ HP.class_ "sidebar"
    , HE.onDragEnterWithOptions (preventDefault <> stopPropagation) DragLeave
    , HP.classList_
        [ ("sidebar-closed", not (model ^. sidebarToggle))
        ]
    ]
    $ one
    $ H.div_
      [ HP.class_ "sidebar-content"
      ]
      [ viewNewProofButton model
      , viewUsage
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
        [ H.li_
            []
            ["Use the buttons at the top of the screen to add lines and subproofs."]
        , H.li_
            []
            ["Drag lines and subproofs to modify the proof."]
        , H.li_
            []
            ["Drag lines and subproofs to the trash can at the top to delete them."]
        , H.li_
            []
            ["Click lines to edit their contents."]
        , H.li_
            []
            ["Check below how to write the symbols and how the rules are defined."]
        ]
    )

{- | For use in 'viewSidebar', returns a list of buttons
that enable the user to change the underlying logic of the proof checker.
-}
viewLogics :: Model -> View Model Action
viewLogics model =
  viewDetails
    "Logics"
    "schema"
    ( H.div_
        [HP.class_ "column-sidebar-content"]
        (map mkLogic [("First-order logic", FOL), ("Propositional Logic", Prop)])
    )
 where
  mkLogic :: (MisoString, Logic) -> View Model Action
  mkLogic (description, l) =
    H.a_
      [ HP.class_ "example-button"
      , HP.classList_ [("disabled", (model ^. logic) == l)]
      , HP.href_ $
          prettyURI $
            URI
              { uriPath = uriPath (model ^. uri)
              , uriFragment = ""
              , uriQueryString = one ("logic", Just $ show l)
              }
      ]
      [text description]

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
      [ HP.class_ "symbol-button"
      ]
      [text $ ms symbol]
  viewSingleSymbol (alias, symbol) =
    H.div_
      [HP.class_ "tooltip-container"]
      [ H.button_
          [ HP.class_ "tooltip-anchor"
          , HP.class_ "symbol-button"
          , HE.onMouseOver (PopOpen (ms alias) True)
          , HE.onMouseOut (PopClose (ms alias))
          ]
          [text $ ms symbol]
      , H.p_
          [ HP.class_ "tooltip-right"
          , HP.id_ (ms alias)
          , textProp "popover" "manual"
          , HP.draggable_ False
          ]
          [text . ms $ "Alias: " <> alias]
      ]

{- | For use in 'viewSidebar',
returns a list of the logic's rules, on hover shows the rule definition.
-}
viewRules :: Model -> View Model Action
viewRules model =
  viewDetails
    "Rules"
    "rule"
    ( H.div_
        [HP.class_ "row-sidebar-content"]
        (map viewSingleRule (toPairs $ model ^. rules))
    )
 where
  viewSingleRule :: (Name, RuleSpec) -> View Model Action
  viewSingleRule (name, rs) =
    H.div_
      [HP.class_ "tooltip-container"]
      [ H.button_
          [ HP.class_ "tooltip-anchor"
          , HP.class_ "rule-button"
          , HE.onMouseOver (PopOpen (ms name) True)
          , HE.onMouseOut (PopClose (ms name))
          ]
          [text $ ms name]
      , H.p_
          [ HP.class_ "tooltip-right"
          , HP.id_ (ms name)
          , onCreatedWith InitMathJAX
          , textProp "popover" "manual"
          , HP.draggable_ False
          ]
          [text . ms $ "\\[(\\mathrm{" <> name <> "})" <> ruleSpecTex rs <> "\\]"]
      ]

{- | For use in 'viewSidebar', returns a list of example t'Proof's,
on hover shows the t'Assumption's and conclusion of the t'Proof'.
-}
viewExamples :: Model -> View Model Action
viewExamples model =
  viewDetails
    "Examples"
    "view_list"
    (H.div_ [HP.class_ "column-sidebar-content"] (map mkExample (model ^. exampleProofs)))
 where
  mkExample :: (Text, Proof) -> View Model Action
  mkExample (name, p) =
    H.div_
      [HP.class_ "tooltip-container"]
      [ H.button_
          [ HP.class_ "tooltip-anchor"
          , HP.class_ "example-button"
          , HE.onMouseOver (PopOpen (ms name) True)
          , HE.onMouseOut (PopClose (ms name))
          , HE.onClick (SetProof p)
          ]
          [text $ ms name]
      , H.p_
          [ HP.class_ "tooltip-right"
          , HP.id_ (ms name)
          , onCreatedWith InitMathJAX
          , textProp "popover" "manual"
          , HP.draggable_ False
          ]
          [text . ms $ proofPreviewTex p]
      ]

------------------------------------------------------------------------------------------

-- ** Proof

{- | Shows the proof workspace of the application, containing a list of line numbers,
a list of formula inputs and a list of rule inputs.
-}
viewProof :: Model -> View Model Action
viewProof model =
  H.div_
    [ HP.class_ "proof-container-border"
    , HE.onDragEnterWithOptions preventDefault DragLeave
    ]
    [ H.div_
        [HP.class_ "proof-container", HE.onDragEnterWithOptions stopPropagation Nop]
        [viewLineNos model, proofView, viewRuleApplications model]
    ]
 where
  proofView =
    H.div_
      [HP.class_ "formulae-container"]
      [_viewProof id id (model ^. proof)]
  _viewProof ::
    (ProofAddr -> ProofAddr) -> (NodeAddr -> NodeAddr) -> Proof -> View Model Action
  _viewProof pa na (SubProof fs ps d) =
    optionalAttrs
      H.div_
      [ HP.class_ "subproof"
      , HP.id_ . show $ pa PAProof
      ]
      (pa PAProof /= PAProof)
      [ HP.class_ "draggable"
      , HP.draggable_ (isNothing (model ^. focusedLine))
      , HP.classList_ [("drag-target", Just (Right (pa PAProof)) == model ^. dragTarget)]
      , HE.onDragStartWithOptions stopPropagation . DragStart . Right $ pa PAProof
      , HE.onDragEndWithOptions defaultOptions DragEnd
      ]
      ( interleaveWithDropZones
          model
          (Just "last-assumption")
          Nothing
          (na . NAAssumption)
          viewAssumptions
          <> interleaveWithDropZones
            model
            Nothing
            (Just (na NAConclusion))
            (na . NALine)
            viewProofs
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
                  (_viewProof (pa . PANested m) (na . NAProof m))
                  e
              )
          )
          0
          ps
    viewConclusion = viewLine model (na NAConclusion) (Right d)

{- | For use in 'viewProof',
returns a list of line numbers that are shown to the left of the t'Proof'.
-}
viewLineNos :: Model -> View Model Action
viewLineNos model =
  H.div_ [HP.class_ "line-no-container"] $
    one $
      goProof 1 id (model ^. proof)
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
          <> interleaveWithDropZones
            model
            Nothing
            (Just (na NAConclusion))
            (na . NALine)
            goPs
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
returns a list of t'RuleApplication's (judgements),
that are shown to the right of the t'Proof'.
-}
viewRuleApplications :: Model -> View Model Action
viewRuleApplications model =
  H.div_ [HP.class_ "rules-container"] $
    one $
      go id (model ^. proof)
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
          <> interleaveWithDropZones
            model
            Nothing
            (Just (na NAConclusion))
            (na . NALine)
            goPs
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
        [ HE.onMouseOver (PopOpen errorBoxId hasError)
        , HE.onMouseOut (PopClose errorBoxId)
        , HP.class_ "rule-container"
        , HP.class_ "tooltip-container"
        , HE.onClick $ Focus (Right na)
        ]
        [ viewErrorBox errorBoxId err
        , H.input_
            [ HP.class_ "rule-input"
            , HP.id_ inputId
            , HP.class_ "tooltip-anchor"
            , HP.classList_
                [ ("has-error", hasError)
                , ("focused", Just (Right na) == model ^. focusedLine)
                ]
            , HP.autocomplete_ False
            , HP.draggable_ False
            , HP.inert_ (Just (Right na) /= model ^. focusedLine)
            , HE.onBlur (Blur (Right na))
            , onWithOptions BUBBLE defaultOptions "input" valueDecoder Input
            , HE.onChange (const Change)
            , HE.onDragStartWithOptions preventDefault Nop
            , HP.value_ ruleTxt
            ]
        ]
   where
    (hasError, ruleTxt, err) = case p of
      (ParsedValid str _) -> (False, ms str, "")
      (ParsedInvalid str err _) -> (True, ms str, ms err)
      (Unparsed str err) -> (True, ms str, ms err)

{- | Returns a errorbox that is shown on hover, containing errors
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
    [ HP.class_ "tooltip-bottom"
    , HP.id_ name
    , textProp "popover" "manual"
    , HP.draggable_ False
    ]
    [text err]

-- | Helper for turning a t'NodeAddr' to a formula inputfield id.
mkFormulaInputId :: NodeAddr -> Proof -> MisoString
mkFormulaInputId na p = "formula-input-" <> show (lineNoOr999 na p)

-- | Helper for turning a t'NodeAddr' to a rule inputfield id.
mkRuleInputId :: NodeAddr -> Proof -> MisoString
mkRuleInputId na p = "rule-input-" <> show (lineNoOr999 na p)

{- | For use in 'viewProof', shows a single line of the t'Proof',
specified by its t'NodeAddr'.
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
      , HP.class_ "tooltip-container"
      , HP.draggable_ (isNothing (model ^. focusedLine))
      , if model ^. focusedLine /= Just (Left na)
          then HE.onDragStartWithOptions stopPropagation $ DragStart (Left na)
          else HE.onDragStartWithOptions (stopPropagation <> preventDefault) Nop
      , HE.onDragEndWithOptions defaultOptions DragEnd
      , HE.onMouseOver (PopOpen errorBoxId hasError)
      , HE.onMouseOut (PopClose errorBoxId)
      , HE.onClick $ Focus (Left na)
      ]
      [ H.input_
          [ HP.inert_ (Just (Left na) /= model ^. focusedLine)
          , HP.id_ inputId
          , HP.class_ "formula-input"
          , HP.class_ "tooltip-anchor"
          , HP.classList_
              [ ("has-error", hasError)
              , ("drag-target", Just (Left na) == model ^. dragTarget)
              , ("draggable", Just (Left na) /= model ^. focusedLine)
              , ("focused", Just (Left na) == model ^. focusedLine)
              ]
          , HP.autocomplete_ False
          , HP.draggable_ False
          , HE.onBlur (Blur (Left na))
          , HE.onChange (const Change)
          , onWithOptions BUBBLE defaultOptions "input" valueDecoder Input
          , HE.onDragStartWithOptions preventDefault Nop
          , HP.value_ txt
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

------------------------------------------------------------------------------------------

-- * Utilities

{- | Helper for viewing material icons based on their name,
see <https://fonts.google.com/icons>
-}
viewMaterialIcon :: MisoString -> View Model Action
viewMaterialIcon name = H.span_ [HP.class_ "material-symbols-outlined"] [text name]

{- |
Shows a dropzone for the given t'NodeAddr',
i.e. a small empty div, where nodes can be dropped.

Expands, if a node can be dropped inside.
-}
viewDropZoneAt ::
  -- | The t'Model'.
  Model ->
  -- | Optional class for the dropzone.
  Maybe MisoString ->
  -- | The corresponding t'NodeAddr'.
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
    , HE.onDragStartWithOptions (preventDefault <> stopPropagation) Nop
    , HE.onDragOverWithOptions preventDefault Nop
    , HE.onDragEnterWithOptions preventDefault (DragEnter na)
    , HE.onDropWithOptions defaultOptions (Drop (LineAddr na))
    ]
    []

-- | Interleaves the list @views@ with dropzones of the corresponding t'NodeAddr'.
interleaveWithDropZones ::
  -- | The t'Model'.
  Model ->
  -- | Optionally a class for the last dropzone.
  Maybe MisoString ->
  -- | Optionally a differing t'NodeAddr' for the last dropzone.
  Maybe NodeAddr ->
  {- | A function for generating t'NodeAddr' from a number
  (e.g. turn @n@ into @v'NAAssumption' n@).
  -}
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

------------------------------------------------------------------------------------------
