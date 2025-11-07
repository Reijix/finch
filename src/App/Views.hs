module App.Views where

import App.Syntax
import qualified Data.List as L
import Data.Maybe (fromJust, fromMaybe)
import Miso
  ( Attribute,
    MisoString,
    Options (..),
    PointerEvent,
    View,
    defaultOptions,
    emptyDecoder,
    focus,
    ms,
    onWithOptions,
    pointerDecoder,
    preventDefault,
    text,
  )
import qualified Miso.Html as HP
import qualified Miso.Html.Element as H
import Miso.Html.Event
import Miso.Html.Property (value_)
import qualified Miso.Html.Property as HP
import Miso.Lens
import Miso.Property (boolProp, textProp)
import Miso.Svg (onFocusOut, text_, tspan_)
import qualified Miso.Svg.Element as S
import qualified Miso.Svg.Property as SP
import Proof.Syntax

viewDragIcon :: View (Model formula rule) Action
viewDragIcon = H.img_ [HP.draggable_ False, HP.src_ "./draggable.svg", HP.height_ "16"]

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
viewBin :: View (Model formula rule) Action
viewBin =
  H.div_
    [ onDragOverWithOptions preventDefault Nop,
      onDragEnterWithOptions preventDefault Nop,
      onDragLeaveWithOptions preventDefault Nop,
      onDropWithOptions defaultOptions (Drop LocationBin),
      HP.class_ "bin"
    ]
    []

viewInsertLineNode :: View (Model formula rule) Action
viewInsertLineNode =
  H.div_
    [ HP.classList_
        [ ("spawn-button", True),
          ("draggable", True)
        ],
      HP.draggable_ True,
      onDragStartWithOptions (Options {_preventDefault = False, _stopPropagation = True}) $ SpawnStart SpawnLine,
      onDragEnd DragEnd
    ]
    []

-- VIEWS
lineContainer ::
  forall formula rule.
  (Show formula) =>
  (Show rule) =>
  Model formula rule -> Bool -> NodeAddr -> MisoString -> View (Model formula rule) Action
lineContainer m isLastAssumption a s =
  H.div_
    [ HP.draggable_ True,
      HP.classList_
        [ ("proof-line", True),
          ("draggable", True),
          ("can-hover", not (m ^. dragging))
        ],
      onDragStartWithOptions (Options {_preventDefault = False, _stopPropagation = True}) $ DragStart a,
      onDragEndWithOptions (Options {_preventDefault = False, _stopPropagation = True}) DragEnd,
      onDoubleClick (DoubleClick a),
      onFocusOut Blur
    ]
    [ H.div_
        [ HP.class_ "upper-hover-zone",
          HP.classList_ [("insert-before", (m ^. currentLineBefore) == Just a)],
          onDragOverWithOptions preventDefault DragOver,
          onDragEnterWithOptions (Options {_preventDefault = True, _stopPropagation = True}) (DragEnter a Before),
          onDragLeaveWithOptions (Options {_preventDefault = True, _stopPropagation = True}) (DragLeave Before),
          onDropWithOptions defaultOptions (Drop (LocationAddr a))
        ]
        [],
      H.div_
        [ HP.class_ "lower-hover-zone",
          HP.classList_ [("insert-after", (m ^. currentLineAfter) == Just a)],
          onDragOverWithOptions preventDefault DragOver,
          onDragEnterWithOptions preventDefault (DragEnter a After),
          onDragLeaveWithOptions preventDefault (DragLeave After),
          onDropWithOptions defaultOptions (Drop (LocationAddr a))
        ]
        [],
      H.input_
        [ inert_ (Just a /= (m ^. focusedLine)),
          HP.id_ . ms $ "proof-line" ++ show (fromJust (fromNodeAddr a (m ^. proof))),
          HP.classList_ [("proof-input", True), ("last-assumption", isLastAssumption)],
          HP.draggable_ False,
          onEnter Nop Blur,
          onInput Input,
          onDragStartWithOptions preventDefault Nop,
          value_ s
        ]
    ]

viewLine ::
  forall formula rule.
  (Show formula) =>
  (Show rule) =>
  Model formula rule ->
  NodeAddr ->
  Bool ->
  Either (Assumption formula) (Derivation formula rule) ->
  View (Model formula rule) Action
viewLine m a isLastAssumption (Left f) = lineContainer m isLastAssumption a $ ms $ show f
-- TODO add container for rules
viewLine m a _ (Right (Derivation f r _)) = lineContainer m False a $ ms $ show f

viewProof ::
  forall formula rule.
  (Show formula) =>
  (Show rule) =>
  Model formula rule -> View (Model formula rule) Action
viewProof model = H.div_ [] [proofView]
  where
    proofView = case model ^. proof of
      ProofLine _ -> error "Tried calling viewProof on a ProofLine"
      SubProof fs ps d -> HP.div_ [HP.class_ "subproof"] (viewAssumptions ++ viewProofs ++ [viewConclusion])
        where
          (_, viewAssumptions) = L.mapAccumL (\n f -> (n + 1, viewLine model (NAAssumption n) (n == 0) (Left f))) 0 fs
          (n, viewProofs) = L.mapAccumL (\n p -> (n + 1, _viewProof n Nothing p)) 0 ps
          viewConclusion = viewLine model (NALine n) False (Right d)
    _viewProof :: Int -> Maybe NodeAddr -> Proof formula rule -> View (Model formula rule) Action
    _viewProof n (Just a) (ProofLine d) = viewLine model (naAppendLine n a) False (Right d)
    _viewProof n ma (SubProof fs ps d) =
      H.div_
        [ HP.class_ "subproof",
          HP.draggable_ True,
          onDragStart $ DragStart a,
          onDragEnd DragEnd
        ]
        (viewAssumptions ++ viewProofs ++ [viewConclusion])
      where
        a = case ma of
          Nothing -> NAProof n Nothing
          Just addr -> addr
        (_, viewAssumptions) = L.mapAccumL (\m f -> (m + 1, viewLine model (naAppendAssumption m a) (m == 0) (Left f))) 0 fs
        (m, viewProofs) = L.mapAccumL (\m p -> (m + 1, _viewProof n (Just a) p)) 0 ps
        viewConclusion = viewLine model (naAppendLine m a) False (Right d)

-----------------------------------------------------------------------------
toEm :: Int -> MisoString
toEm n = ms (show n ++ "em")