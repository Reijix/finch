module App.Views where

import App.Model
import Data.Either (isLeft)
import Data.List qualified as L
import Data.Maybe (fromJust, fromMaybe)
import Fitch.Proof
import Miso (
  Attribute,
  MisoString,
  Options (..),
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

inert_ :: Bool -> Attribute action
inert_ = boolProp "inert"

-----------------------------------------------------------------------------
-- disable text-highlighting during drag and drop. `preventDefault`
onPD :: (PointerEvent -> Action) -> Attribute Action
onPD f =
  onWithOptions
    preventDefault
    "pointerdown"
    pointerDecoder
    (\action _ -> f action)

-----------------------------------------------------------------------------
conditionalList :: [(Bool, a)] -> [a]
conditionalList [] = []
conditionalList ((True, x) : xs) = x : conditionalList xs
conditionalList ((False, _) : xs) = conditionalList xs

viewErrorIcon :: MisoString -> View Model Action
viewErrorIcon err = H.img_ [HP.draggable_ False, HP.src_ "./error-icon.svg", HP.height_ "16", HP.title_ err]

viewBin :: View Model Action
viewBin =
  H.div_
    [ onDragOverWithOptions preventDefault Nop
    , onDragEnterWithOptions preventDefault Nop
    , onDragLeaveWithOptions preventDefault Nop
    , onDropWithOptions defaultOptions (Drop LocationBin)
    , HP.class_ "bin"
    ]
    [H.p_ [] ["Delete Node"]]

viewSpawnNode :: SpawnType -> String -> View Model Action
viewSpawnNode tp str =
  H.div_
    [ HP.classList_
        [ ("spawn-button", True)
        , ("draggable", True)
        ]
    , HP.draggable_ True
    , onDragStartWithOptions (Options{_preventDefault = False, _stopPropagation = True}) $ SpawnStart tp
    , onDragEnd DragEnd
    ]
    [H.p_ [] [text $ ms str]]

-- VIEWS
viewLine :: Model -> NodeAddr -> Bool -> Either Assumption Derivation -> View Model Action
viewLine m a isLastAssumption e =
  H.div_
    [ HP.draggable_ $ (m ^. focusedLine) /= Just a
    , HP.classList_
        [ ("proof-line", True)
        , ("draggable", (m ^. focusedLine) /= Just a)
        , ("can-hover", not (m ^. dragging))
        ]
    , onDragStartWithOptions stopPropagation $ DragStart a
    , onDragEndWithOptions stopPropagation DragEnd
    , onDoubleClick (DoubleClick a)
    , onFocusOut Blur
    ]
    [ H.div_
        [ HP.class_ "upper-hover-zone"
        , HP.classList_ [("insert-before", m ^. currentLineBefore == Just a)]
        , -- hide while focused, so that the input field is clickable for mouse movement
          HP.hidden_ $ m ^. focusedLine == Just a
        , onDragOverWithOptions (Options{_preventDefault = True, _stopPropagation = True}) Nop
        , onDragEnterWithOptions (Options{_preventDefault = True, _stopPropagation = True}) (DragEnter a Before)
        , onDragLeaveWithOptions (Options{_preventDefault = True, _stopPropagation = True}) (DragLeave Before)
        , onDropWithOptions (Options{_preventDefault = True, _stopPropagation = True}) (Drop (LocationAddr a Before))
        ]
        []
    , H.div_
        [ HP.class_ "lower-hover-zone"
        , HP.classList_ [("insert-after", m ^. currentLineAfter == Just a)]
        , -- hide while focused, so that the input field is clickable for mouse movement
          HP.hidden_ $ m ^. focusedLine == Just a
        , onDragOverWithOptions (Options{_preventDefault = True, _stopPropagation = True}) Nop
        , onDragEnterWithOptions (Options{_preventDefault = True, _stopPropagation = True}) (DragEnter a After)
        , onDragLeaveWithOptions (Options{_preventDefault = True, _stopPropagation = True}) (DragLeave After)
        , onDropWithOptions (Options{_preventDefault = True, _stopPropagation = True}) (Drop (LocationAddr a After))
        ]
        []
    , -- TODO RULES
      H.div_
        [HP.class_ "line-container"]
        $ conditionalList
          [
            ( True
            , H.input_
                [ inert_ (Just a /= m ^. focusedLine)
                , HP.id_ . ms $ "proof-line" ++ show (fromJust (fromNodeAddr a (m ^. proof)))
                , HP.classList_
                    [ ("proof-input", True)
                    , ("last-assumption", isLastAssumption)
                    , ("parse-success", parseSuccess)
                    , ("parse-fail", not parseSuccess)
                    ]
                , HP.draggable_ False
                , onWithOptions defaultOptions "input" valueDecoder Input
                , onCreatedWith (KeyDownStart a)
                , onBeforeDestroyed (KeyDownStop a)
                , onDragStartWithOptions preventDefault Nop
                , value_ txt
                ]
            )
          ,
            ( True
            , H.input_
                [value_ "rule"]
            )
          ,
            ( not parseSuccess
            , viewErrorIcon err
            )
          ]
    ]
 where
  (parseSuccess, txt, err) = case e of
    Left a -> case a of
      Parsed str a' -> (True, ms str, "")
      Unparsed str err -> (False, ms str, ms err)
    Right (Derivation f _) -> case f of
      Parsed str f' -> (True, ms str, "")
      Unparsed str err -> (False, ms str, ms err)

viewProof :: Model -> View Model Action
viewProof model = H.div_ [] [proofView]
 where
  proofView = case model ^. proof of
    ProofLine _ -> error "Tried calling viewProof on a ProofLine"
    SubProof fs ps d -> H.div_ [HP.class_ "subproof"] (viewAssumptions ++ viewProofs ++ [viewConclusion])
     where
      (_, viewAssumptions) = L.mapAccumL (\n f -> (n + 1, viewLine model (NAAssumption n) (n == L.length fs - 1) (Left f))) 0 fs
      (n, viewProofs) = L.mapAccumL (\n p -> (n + 1, _viewProof n Nothing p)) 0 ps
      viewConclusion = viewLine model NAConclusion False (Right d)
  _viewProof :: Int -> Maybe NodeAddr -> Proof -> View Model Action
  _viewProof n Nothing (ProofLine d) = viewLine model (NAProof n Nothing) False (Right d)
  _viewProof n (Just a) (ProofLine d) = viewLine model (naAppendProof n a) False (Right d)
  _viewProof n ma (SubProof fs ps d) =
    H.div_
      [ HP.class_ "subproof"
      , HP.draggable_ True
      , onDragStartWithOptions stopPropagation $ DragStart a
      , onDragEndWithOptions stopPropagation DragEnd
      ]
      (viewAssumptions ++ viewProofs ++ [viewConclusion])
   where
    a = case ma of
      Nothing -> NAProof n Nothing
      Just addr -> naAppendProof n addr
    (_, viewAssumptions) = L.mapAccumL (\m f -> (m + 1, viewLine model (naAppendAssumption m a) (m == L.length fs - 1) (Left f))) 0 fs
    (m, viewProofs) = L.mapAccumL (\m p -> (m + 1, _viewProof m (Just a) p)) 0 ps
    viewConclusion = viewLine model (naAppendConclusion a) False (Right d)

-----------------------------------------------------------------------------
toEm :: Int -> MisoString
toEm n = ms (show n ++ "em")