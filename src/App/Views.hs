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
    , onDragEndWithOptions stopPropagation DragEnd
    ]
    [H.p_ [] [text $ ms str]]

-- VIEWS
viewLine :: Model -> NodeAddr -> Bool -> Either Assumption Derivation -> View Model Action
viewLine model addr isLastAssumption e =
  H.div_
    [ HP.draggable_ $ (model ^. focusedLine) /= Just (Left addr)
    , HP.classList_
        [ ("proof-line", True)
        , ("draggable", (model ^. focusedLine) /= Just (Left addr))
        , ("can-hover", not (model ^. dragging))
        ]
    , HP.hidden_ False
    , onDragStartWithOptions stopPropagation $ DragStart addr
    , onDragEndWithOptions stopPropagation DragEnd
    ]
    [ H.div_
        [ HP.class_ "upper-hover-zone"
        , HP.classList_ [("insert-before", model ^. currentLineBefore == Just addr), ("no-pointer-events", not (model ^. dragging))]
        , -- hide while focused, so that the input field is clickable for mouse movement
          HP.hidden_ $ model ^. focusedLine == Just (Left addr)
        , onDragOverWithOptions (preventDefault <> stopPropagation) Nop
        , onDragEnterWithOptions (preventDefault <> stopPropagation) (DragEnter addr Before)
        , onDragLeaveWithOptions (preventDefault <> stopPropagation) (DragLeave Before)
        , onDropWithOptions (preventDefault <> stopPropagation) (Drop (LocationAddr addr Before))
        ]
        []
    , H.div_
        [ HP.class_ "lower-hover-zone"
        , HP.classList_ [("insert-after", model ^. currentLineAfter == Just addr), ("no-pointer-events", not (model ^. dragging))]
        , -- hide while focused, so that the input field is clickable for mouse movement
          HP.hidden_ $ model ^. focusedLine == Just (Left addr)
        , onDragOverWithOptions (preventDefault <> stopPropagation) Nop
        , onDragEnterWithOptions (preventDefault <> stopPropagation) (DragEnter addr After)
        , onDragLeaveWithOptions (preventDefault <> stopPropagation) (DragLeave After)
        , onDropWithOptions (preventDefault <> stopPropagation) (Drop (LocationAddr addr After))
        ]
        []
    , H.div_
        [ onDoubleClick $ DoubleClick (Left addr)
        , HP.class_ "formula-container"
        , HP.hidden_ False
        , HP.classList_ [("has-error", not parseSuccess || not semanticSuccess)]
        ]
        [ H.code_ [HP.class_ "error", HP.draggable_ False] [text err]
        , H.input_
            [ HP.inert_ (Just (Left addr) /= model ^. focusedLine)
            , HP.id_ . ms $ "proof-line" ++ show (fromJust (fromNodeAddr addr (model ^. proof)))
            , HP.classList_
                [ ("formula-input", True)
                , ("last-assumption", isLastAssumption)
                , ("parse-success", parseSuccess && semanticSuccess)
                , ("parse-fail", not parseSuccess || not semanticSuccess)
                , ("draggable", Just (Left addr) /= model ^. focusedLine)
                ]
            , HP.draggable_ False
            , onBlur Blur
            , onChange (const Change)
            , onWithOptions BUBBLE defaultOptions "input" valueDecoder Input
            , onCreatedWith (KeyDownStart (Left addr))
            , onBeforeDestroyed (KeyDownStop (Left addr))
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

viewProof :: Model -> View Model Action
viewProof model = H.div_ [HP.class_ "proof-container"] [lineNos, proofView, rules]
 where
  rules = H.div_ [HP.class_ "rules-container"] $ pSerializeWithAddr mapAssumption mapDerivation (model ^. proof)
   where
    mapAssumption :: Assumption -> NodeAddr -> View Model Action
    mapAssumption a addr = H.p_ [HP.class_ "empty-rule"] []
    mapDerivation :: Derivation -> NodeAddr -> View Model Action
    mapDerivation (Derivation _ p) addr =
      H.div_
        [ onDoubleClick $ DoubleClick (Right addr)
        , HP.class_ "rule-container"
        , HP.classList_ [("non-selectable", Just (Right addr) /= model ^. focusedLine), ("has-error", not parseSuccess || not semanticSuccess)]
        ]
        [ H.code_ [HP.class_ "error", HP.draggable_ False] [text err]
        , H.input_
            [ HP.class_ "rule-input"
            , HP.id_ . ms $ "proof-line-rule" ++ show (fromJust (fromNodeAddr addr (model ^. proof)))
            , HP.classList_
                [ ("parse-success", parseSuccess && semanticSuccess)
                , ("parse-fail", not parseSuccess || not semanticSuccess)
                ]
            , HP.draggable_ False
            , HP.inert_ (Just (Right addr) /= model ^. focusedLine)
            , onBlur Blur
            , onWithOptions BUBBLE defaultOptions "input" valueDecoder Input
            , onChange (const Change)
            , onCreatedWith (KeyDownStart (Right addr))
            , onBeforeDestroyed (KeyDownStop (Right addr))
            , onDragStartWithOptions preventDefault Nop
            , value_ ruleTxt
            ]
        ]
     where
      (semanticSuccess, parseSuccess, ruleTxt, err) = case p of
        (ParsedValid str _) -> (True, True, ms str, "")
        (ParsedInvalid str err _) -> (False, True, ms str, ms err)
        (Unparsed str err) -> (False, False, ms str, ms err)
  lineNos =
    H.div_ [HP.class_ "line-no-container"] $
      map
        (\n -> H.p_ [HP.class_ "line-no"] [text $ ms n])
        (take (pLength $ model ^. proof) [1 :: Int ..])
  proofView = case model ^. proof of
    ProofLine _ -> error "Tried calling viewProof on a ProofLine"
    SubProof fs ps d -> H.div_ [HP.class_ "outer-subproof"] (viewAssumptions ++ viewProofs ++ [viewConclusion])
     where
      (_, viewAssumptions) = L.mapAccumL (\n f -> (n + 1, viewLine model (NAAssumption n) (n == L.length fs - 1) (Left f))) 0 fs
      (n, viewProofs) = L.mapAccumL (\n p -> (n + 1, _viewProof n Nothing p)) 0 ps
      viewConclusion = viewLine model NAConclusion False (Right d)
  _viewProof :: Int -> Maybe NodeAddr -> Proof -> View Model Action
  _viewProof n ma (ProofLine d) = viewLine model (naAppendProof n ma) False (Right d)
  _viewProof n ma (SubProof fs ps d) =
    H.div_
      [ HP.class_ "subproof"
      , HP.draggable_ True
      , HP.hidden_ False
      , onDragStartWithOptions stopPropagation $ DragStart a
      , onDragEndWithOptions stopPropagation DragEnd
      ]
      (viewAssumptions ++ viewProofs ++ [viewConclusion])
   where
    a = naAppendProof n ma
    (_, viewAssumptions) = L.mapAccumL (\m f -> (m + 1, viewLine model (naAppendAssumption m (Just $ naAppendProof n ma)) (m == L.length fs - 1) (Left f))) 0 fs
    (m, viewProofs) = L.mapAccumL (\m p -> (m + 1, _viewProof m (Just a) p)) 0 ps
    viewConclusion = viewLine model (naAppendConclusion $ Just a) False (Right d)

-----------------------------------------------------------------------------
toEm :: Int -> MisoString
toEm n = ms (show n ++ "em")