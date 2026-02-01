module App.Views where

import App.Model
import Data.Either (isLeft)
import Data.List qualified as L
import Data.Maybe (fromJust, fromMaybe)
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
  keyInfoDecoder,
  ms,
  onBeforeDestroyed,
  onCreatedWith,
  onWithOptions,
  pointerDecoder,
  preventDefault,
  stopPropagation,
  text,
  textRaw,
  valueDecoder,
 )
import Miso.Html.Element qualified as H
import Miso.Html.Event
import Miso.Html.Property (value_)
import Miso.Html.Property qualified as HP
import Miso.Lens
import Miso.Property (boolProp, textProp)
import Miso.Svg (onFocusOut, onMouseDown, text_, tspan_)
import Miso.Svg.Element qualified as S
import Miso.Svg.Property qualified as SP

contentEditable_ :: Bool -> Attribute action
contentEditable_ = boolProp "contentEditable"

-----------------------------------------------------------------------------
viewBin :: View Model Action
viewBin =
  H.div_
    [ onDragOverWithOptions preventDefault Nop
    , onDragEnterWithOptions preventDefault Nop
    , onDragLeaveWithOptions preventDefault Nop
    , onDropWithOptions defaultOptions (Drop LocationBin)
    , HP.class_ "bin"
    ]
    [H.p_ [] ["Delete"]]

viewSpawnNode :: SpawnType -> String -> View Model Action
viewSpawnNode tp str =
  H.div_
    [ HP.classList_
        [ ("spawn-button", True)
        , ("draggable", True)
        ]
    , HP.draggable_ True
    , onDragStartWithOptions stopPropagation $ SpawnStart tp
    , onDragEndWithOptions defaultOptions DragEnd
    ]
    [H.p_ [] [text $ ms str]]

-- VIEWS
viewLine :: Model -> NodeAddr -> Bool -> Either Assumption Derivation -> View Model Action
viewLine model na isLastAssumption e =
  H.div_
    [ HP.draggable_ $ (model ^. focusedLine) /= Just (Left na)
    , HP.classList_
        [ ("proof-line", True)
        , ("draggable", (model ^. focusedLine) /= Just (Left na))
        , ("can-hover", not (model ^. dragging))
        ]
    , HP.hidden_ False
    , onDragStartWithOptions stopPropagation $ DragStart (Left na)
    , onDragEndWithOptions defaultOptions DragEnd
    ]
    [ H.div_
        [ HP.class_ "upper-hover-zone"
        , HP.classList_
            [ ("insert-before", model ^. currentLineBefore == Just na)
            , ("no-pointer-events", not (model ^. dragging))
            ]
        , -- hide while focused, so that the input field is clickable for mouse movement
          HP.hidden_ $ model ^. focusedLine == Just (Left na)
        , onDragOverWithOptions (preventDefault <> stopPropagation) Nop
        , onDragEnterWithOptions (preventDefault <> stopPropagation) (DragEnter na Before)
        , onDragLeaveWithOptions (preventDefault <> stopPropagation) (DragLeave Before)
        , onDropWithOptions (preventDefault <> stopPropagation) (Drop (LocationAddr na Before))
        ]
        []
    , H.div_
        [ HP.class_ "lower-hover-zone"
        , HP.classList_
            [ ("insert-after", model ^. currentLineAfter == Just na)
            , ("no-pointer-events", not (model ^. dragging))
            ]
        , -- hide while focused, so that the input field is clickable for mouse movement
          HP.hidden_ $ model ^. focusedLine == Just (Left na)
        , onDragOverWithOptions (preventDefault <> stopPropagation) Nop
        , onDragEnterWithOptions (preventDefault <> stopPropagation) (DragEnter na After)
        , onDragLeaveWithOptions (preventDefault <> stopPropagation) (DragLeave After)
        , onDropWithOptions (preventDefault <> stopPropagation) (Drop (LocationAddr na After))
        ]
        []
    , H.div_
        [ onDoubleClick $ DoubleClick (Left na)
        , HP.class_ "formula-container"
        , HP.hidden_ False
        , HP.classList_ [("has-error", not parseSuccess || not semanticSuccess)]
        ]
        [ H.code_ [HP.class_ "error", HP.draggable_ False] [text err]
        , H.input_
            [ HP.inert_ (Just (Left na) /= model ^. focusedLine)
            , HP.id_ . ms $ "proof-line" ++ show (fromJust (fromNodeAddr na (model ^. proof)))
            , HP.classList_
                [ ("formula-input", True)
                , ("last-assumption", isLastAssumption)
                , ("parse-success", parseSuccess && semanticSuccess)
                , ("parse-fail", not parseSuccess || not semanticSuccess)
                , ("draggable", Just (Left na) /= model ^. focusedLine)
                ]
            , HP.draggable_ False
            , onBlur Blur
            , onChange (const Change)
            , onWithOptions BUBBLE defaultOptions "input" valueDecoder Input
            , onCreatedWith (KeyDownStart (Left na))
            , onBeforeDestroyed (KeyDownStop (Left na))
            , onDragStartWithOptions preventDefault Nop
            , value_ txt
            ]
        ]
    ]
 where
  (semanticSuccess, parseSuccess, txt, err) = case e of
    Left a -> case a of
      ParsedValid str a' -> (True, True, ms str, "")
      ParsedInvalid str err a' -> (False, True, ms str, ms err)
      Unparsed str err -> (False, False, ms str, ms err)
    Right (Derivation f r) -> case f of
      (ParsedValid str f') -> (True, True, ms str, "")
      (ParsedInvalid str err f') -> (False, True, ms str, ms err)
      (Unparsed str err) -> (False, False, ms str, ms err)

viewLineNos :: Model -> View Model Action
viewLineNos model = H.div_ [HP.class_ "line-no-container"] . snd $ go 1 (model ^. proof)
 where
  go :: Int -> Proof -> (Int, [View Model Action])
  go n (SubProof fs ps c) = (n'' + 1, fsNos <> concat psNos <> one (lineNoFor n''))
   where
    lineNoFor :: Int -> View Model Action
    lineNoFor = H.p_ [HP.class_ "line-no"] . one . text . ms
    (n', fsNos) = case fs of
      [] -> (n, one $ H.p_ [HP.class_ "empty-line-no"] [])
      _ -> mapAccumL (\s _ -> (s + 1, lineNoFor s)) n fs
    (n'', psNos) = mapAccumL (\s -> either (const (s + 1, one $ lineNoFor s)) (\p -> (fst (go s p), snd $ go s p))) n' ps

viewRules :: Model -> View Model Action
viewRules model = H.div_ [HP.class_ "rules-container"] $ go id (model ^. proof)
 where
  go :: (NodeAddr -> NodeAddr) -> Proof -> [View Model Action]
  go na (SubProof fs ps c) = goFs <> concat goPs <> one goC
   where
    goFs = case fs of
      [] -> one $ H.p_ [HP.class_ "empty-assumption-rule"] []
      _ -> map (const $ H.p_ [HP.class_ "empty-rule"] []) fs
    goPs = snd $ mapAccumL (\n e -> (n + 1, either (one . goDerivation (na $ NALine n)) (go (na . NAProof n)) e)) 0 ps
    goC = goDerivation (na NAConclusion) c
  goDerivation :: NodeAddr -> Derivation -> View Model Action
  goDerivation na (Derivation _ p) =
    H.div_
      [ onDoubleClick $ DoubleClick (Right na)
      , HP.class_ "rule-container"
      , HP.classList_
          [ ("non-selectable", Just (Right na) /= model ^. focusedLine)
          , ("has-error", not parseSuccess || not semanticSuccess)
          ]
      ]
      [ H.code_ [HP.class_ "error", HP.draggable_ False] [text err]
      , H.input_
          [ HP.class_ "rule-input"
          , HP.id_ . ms $ "proof-line-rule" ++ show (fromJust (fromNodeAddr na (model ^. proof)))
          , HP.classList_
              [ ("parse-success", parseSuccess && semanticSuccess)
              , ("parse-fail", not parseSuccess || not semanticSuccess)
              ]
          , HP.draggable_ False
          , HP.inert_ (Just (Right na) /= model ^. focusedLine)
          , onBlur Blur
          , onWithOptions BUBBLE defaultOptions "input" valueDecoder Input
          , onChange (const Change)
          , onCreatedWith (KeyDownStart (Right na))
          , onBeforeDestroyed (KeyDownStop (Right na))
          , onDragStartWithOptions preventDefault Nop
          , value_ ruleTxt
          ]
      ]
   where
    (semanticSuccess, parseSuccess, ruleTxt, err) = case p of
      (ParsedValid str _) -> (True, True, ms str, "")
      (ParsedInvalid str err _) -> (False, True, ms str, ms err)
      (Unparsed str err) -> (False, False, ms str, ms err)

viewProof :: Model -> View Model Action
viewProof model = H.div_ [HP.class_ "proof-container"] [viewLineNos model, proofView, viewRules model]
 where
  proofView = H.div_ [HP.class_ "formulae-container"] (viewAssumptions ++ viewProofs ++ [viewConclusion])
   where
    (SubProof fs ps d) = model ^. proof
    viewAssumptions = case fs of
      [] -> one $ H.p_ [HP.class_ "empty-assumptions"] []
      _ ->
        snd $
          L.mapAccumL
            (\n f -> (n + 1, viewLine model (NAAssumption n) (n == length fs - 1) (Left f)))
            0
            fs
    viewProofs =
      snd $
        L.mapAccumL
          (\n e -> (n + 1, either (viewLine model (NALine n) False . Right) (_viewProof (PAProof n) (NAProof n)) e))
          0
          ps
    viewConclusion = viewLine model NAConclusion False (Right d)
  _viewProof :: ProofAddr -> (NodeAddr -> NodeAddr) -> Proof -> View Model Action
  _viewProof pa na (SubProof fs ps d) =
    H.div_
      [ HP.class_ "subproof"
      , HP.draggable_ True
      , HP.hidden_ False
      , onDragStartWithOptions stopPropagation $ DragStart (Right pa)
      , onDragEndWithOptions defaultOptions DragEnd
      ]
      (viewAssumptions ++ viewProofs ++ [viewConclusion])
   where
    viewAssumptions = case fs of
      [] -> one $ H.p_ [HP.class_ "empty-assumptions"] []
      _ ->
        snd $
          L.mapAccumL
            ( \m f ->
                ( m + 1
                , viewLine
                    model
                    (na (NAAssumption m))
                    (m == length fs - 1)
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
                  (viewLine model (na $ NALine m) False . Right)
                  (_viewProof (paProofToNested pa $ PAProof m) (na . NAProof m))
                  e
              )
          )
          0
          ps
    viewConclusion = viewLine model (na NAConclusion) False (Right d)

-----------------------------------------------------------------------------
toEm :: Int -> MisoString
toEm n = ms (show n ++ "em")