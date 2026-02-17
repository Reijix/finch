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
import Miso.Html.Element qualified as H
import Miso.Html.Event
import Miso.Html.Property (value_)
import Miso.Html.Property qualified as HP
import Miso.Lens
import Miso.Property (boolProp, textProp)
import Miso.Svg (onFocusOut, onMouseDown, text_, tspan_)
import Miso.Svg.Element qualified as S
import Miso.Svg.Property qualified as SP
import Util (interleave)

contentEditable_ :: Bool -> Attribute action
contentEditable_ = boolProp "contentEditable"

interleaveWithDropZones :: Model -> Maybe MisoString -> (Int -> NodeAddr) -> [View Model Action] -> [View Model Action]
interleaveWithDropZones model mclass na views = interleave dropzones views
 where
  dropzones :: [View Model Action]
  dropzones =
    map
      ( \n ->
          H.div_
            [ HP.class_ "drop-zone"
            , HP.classList_
                [ ("expanded-drop-zone", model ^. currentHoverLine == Just (na n))
                , (fromMaybe "" mclass, n == length views && isJust mclass)
                ]
            , HP.draggable_ False
            , onDragOverWithOptions preventDefault Nop
            , onDragEnterWithOptions preventDefault (DragEnter (na n))
            , onDropWithOptions defaultOptions (Drop (LocationAddr (na n)))
            ]
            []
      )
      [0 .. length views + 1]

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
viewLine :: Model -> NodeAddr -> Either Assumption Derivation -> View Model Action
viewLine model na e =
  H.div_
    [ HP.class_ "proof-line"
    , HP.classList_ [("has-error", not parseSuccess || not semanticSuccess), ("can-hover", not (model ^. dragging))]
    ]
    [ optionalAttrs
        H.div_
        [ HP.draggable_ $ na /= NAConclusion && (model ^. focusedLine) /= Just (Left na)
        , HP.classList_
            [ -- ("proof-line", True)
              ("draggable", na /= NAConclusion && (model ^. focusedLine) /= Just (Left na))
            , ("can-hover", not (model ^. dragging))
            , ("non-selectable", na == NAConclusion)
            ]
        ]
        (not $ isNAConclusion na)
        [ onDragStartWithOptions stopPropagation $ DragStart (Left na)
        , onDragEndWithOptions defaultOptions DragEnd
        ]
        [ H.div_
            [ onDoubleClick $ DoubleClick (Left na)
            , HP.class_ "formula-container"
            ]
            -- TODO fix another way!
            [ H.input_
                [ HP.inert_ (Just (Left na) /= model ^. focusedLine)
                , HP.id_ . ms $ "proof-line" ++ show (lineNoOr999 na (model ^. proof))
                , HP.classList_
                    [ ("formula-input", True)
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
    , H.code_ [HP.class_ "error", HP.draggable_ False, HP.hidden_ (parseSuccess && semanticSuccess)] [text err]
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
viewLineNos model = H.div_ [HP.class_ "line-no-container"] $ one $ goProof 1 id (model ^. proof)
 where
  lineNoFor :: Int -> View Model Action
  lineNoFor = H.p_ [HP.class_ "line-no", HP.draggable_ False] . one . text . ms
  goProof :: Int -> (NodeAddr -> NodeAddr) -> Proof -> View Model Action
  goProof lineNo na (SubProof fs ps c) =
    H.div_
      [HP.class_ "line-no-wrapper", HP.draggable_ False]
      ( interleaveWithDropZones model (Just "empty-last-assumption") (na . NAAssumption) goFs
          <> interleaveWithDropZones model Nothing (na . NALine) goPs
          <> one goC
      )
   where
    ((lineNo', _), goFs) = case fs of
      [] -> ((lineNo, 0), one $ H.p_ [HP.class_ "empty-assumption-rule"] [])
      _ -> mapAccumL (\(lineNo, d) f -> ((lineNo + 1, d + 1), lineNoFor lineNo)) (lineNo, 0) fs
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
      ( interleaveWithDropZones model (Just "empty-last-assumption") (na . NAAssumption) goFs
          <> interleaveWithDropZones model Nothing (na . NALine) goPs
          <> one goC
      )
   where
    goFs = case fs of
      [] -> one $ H.p_ [HP.class_ "empty-assumption-rule"] []
      _ -> map (const $ H.p_ [HP.class_ "empty-rule"] []) fs
    goPs =
      snd $
        mapAccumL
          (\n e -> (n + 1, either (goDerivation (na $ NALine n)) (go (na . NAProof n)) e))
          0
          ps
    goC = goDerivation (na NAConclusion) c
  goDerivation :: NodeAddr -> Derivation -> View Model Action
  goDerivation na (Derivation _ p) =
    H.div_
      [ onDoubleClick $ DoubleClick (Right na)
      , HP.class_ "rule-container"
      , HP.classList_
          [ ("non-selectable", Just (Right na) /= model ^. focusedLine)
          , ("has-error", not parseSuccess || not semanticSuccess)
          , ("can-hover", not (model ^. dragging))
          ]
      ]
      [ H.code_ [HP.class_ "error", HP.draggable_ False] [text err]
      , H.input_
          [ HP.class_ "rule-input"
          , HP.id_ . ms $ "proof-line-rule" ++ show (lineNoOr999 na (model ^. proof))
          , HP.classList_
              [("parse-fail", not parseSuccess || not semanticSuccess)]
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
viewProof model =
  H.div_
    [ HP.class_ "proof-container-border"
    , onDragEnterWithOptions preventDefault DragLeave
    ]
    . one
    $ H.div_
      [HP.class_ "proof-container", onDragEnterWithOptions stopPropagation Nop]
      [viewLineNos model, proofView, viewRules model]
 where
  proofView =
    H.div_
      [HP.class_ "formulae-container"]
      ( interleaveWithDropZones model (Just "last-assumption") NAAssumption viewAssumptions
          <> interleaveWithDropZones model Nothing NALine viewProofs
          <> one viewConclusion
      )
   where
    (SubProof fs ps d) = model ^. proof
    viewAssumptions = case fs of
      [] -> one $ H.p_ [HP.class_ "empty-assumptions"] []
      _ ->
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
      , HP.draggable_ True
      , onDragStartWithOptions stopPropagation $ DragStart (Right pa)
      , onDragEndWithOptions defaultOptions DragEnd
      ]
      ( interleaveWithDropZones model (Just "last-assumption") (na . NAAssumption) viewAssumptions
          <> interleaveWithDropZones model Nothing (na . NALine) viewProofs
          <> one viewConclusion
      )
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
toEm :: Int -> MisoString
toEm n = ms (show n ++ "em")