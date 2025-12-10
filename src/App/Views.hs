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
import Miso qualified as HP
import Miso.CSS qualified as HP
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

viewErrorIcon :: MisoString -> View Model Action
viewErrorIcon err =
  H.div_
    [HP.class_ "error"]
    [ H.img_
        [ HP.draggable_ False
        , HP.src_ "./error-icon.svg"
        , HP.height_ "16"
        , HP.width_ "16"
        ]
    , H.code_ [HP.draggable_ False] [text err]
    ]

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
    , onDragStartWithOptions stopPropagation $ SpawnStart tp
    , onDragEndWithOptions stopPropagation DragEnd
    ]
    [H.p_ [] [text $ ms str]]

-- VIEWS
viewLine :: Model -> Int -> NodeAddr -> Bool -> Either Assumption Derivation -> View Model Action
viewLine m n a isLastAssumption e =
  H.div_
    [ HP.draggable_ $ (m ^. focusedLine) /= Just (Left a)
    , HP.classList_
        [ ("proof-line", True)
        , ("draggable", (m ^. focusedLine) /= Just (Left a))
        , ("can-hover", not (m ^. dragging))
        ]
    , HP.hidden_ False
    , HP.intProp "data-line-no" (n + 1)
    , onDragStartWithOptions stopPropagation $ DragStart a
    , onDragEndWithOptions stopPropagation DragEnd
    , onBlur Blur
    ]
    ( [ H.div_
          [ HP.class_ "upper-hover-zone"
          , HP.classList_ [("insert-before", m ^. currentLineBefore == Just a), ("no-pointer-events", not (m ^. dragging))]
          , -- hide while focused, so that the input field is clickable for mouse movement
            HP.hidden_ $ m ^. focusedLine == Just (Left a)
          , onDragOverWithOptions (preventDefault <> stopPropagation) Nop
          , onDragEnterWithOptions (preventDefault <> stopPropagation) (DragEnter a Before)
          , onDragLeaveWithOptions (preventDefault <> stopPropagation) (DragLeave Before)
          , onDropWithOptions (preventDefault <> stopPropagation) (Drop (LocationAddr a Before))
          ]
          []
      , H.div_
          [ HP.class_ "lower-hover-zone"
          , HP.classList_ [("insert-after", m ^. currentLineAfter == Just a), ("no-pointer-events", not (m ^. dragging))]
          , -- hide while focused, so that the input field is clickable for mouse movement
            HP.hidden_ $ m ^. focusedLine == Just (Left a)
          , onDragOverWithOptions (preventDefault <> stopPropagation) Nop
          , onDragEnterWithOptions (preventDefault <> stopPropagation) (DragEnter a After)
          , onDragLeaveWithOptions (preventDefault <> stopPropagation) (DragLeave After)
          , onDropWithOptions (preventDefault <> stopPropagation) (Drop (LocationAddr a After))
          ]
          []
      , H.div_ [HP.class_ "line-no"] [text $ ms $ show $ fromJust (fromNodeAddr a (m ^. proof))]
      , H.div_
          [HP.class_ "formula-rule-container"]
          ( H.div_
              [ onDoubleClick $ DoubleClick (Left a)
              , HP.class_ "formula-container"
              , HP.classList_ [("to-foreground", Just (Left a) /= m ^. focusedLine)]
              ]
              [ H.input_
                  [ HP.inert_ (Just (Left a) /= m ^. focusedLine)
                  , HP.id_ . ms $ "proof-line" ++ show (fromJust (fromNodeAddr a (m ^. proof)))
                  , HP.classList_
                      [ ("formula-input", True)
                      , ("last-assumption", isLastAssumption)
                      , ("parse-success", parseSuccessFormula)
                      , ("parse-fail", not parseSuccessFormula)
                      , ("draggable", Just (Left a) /= m ^. focusedLine)
                      , ("to-foreground", Just (Left a) == m ^. focusedLine)
                      ]
                  , HP.draggable_ False
                  , onWithOptions BUBBLE defaultOptions "input" valueDecoder Input
                  , onCreatedWith (KeyDownStart (Left a))
                  , onBeforeDestroyed (KeyDownStop (Left a))
                  , onDragStartWithOptions preventDefault Nop
                  , value_ txt
                  ]
              ]
              : [ H.div_
                    [ onDoubleClick $ DoubleClick (Right a)
                    , HP.class_ "rule-container"
                    , HP.classList_ [("to-foreground", Just (Right a) /= m ^. focusedLine)]
                    ]
                    [ H.input_
                        [ HP.class_ "rule-input"
                        , HP.id_ . ms $ "proof-line-rule" ++ show (fromJust (fromNodeAddr a (m ^. proof)))
                        , HP.classList_
                            [ ("parse-success", parseSuccessRule)
                            , ("parse-fail", not parseSuccessRule)
                            , ("draggable", Just (Right a) /= m ^. focusedLine)
                            , ("to-foreground", Just (Right a) == m ^. focusedLine)
                            ]
                        , HP.draggable_ False
                        , HP.inert_ (Just (Right a) /= m ^. focusedLine)
                        , onWithOptions BUBBLE defaultOptions "input" valueDecoder Input
                        , onCreatedWith (KeyDownStart (Right a))
                        , onBeforeDestroyed (KeyDownStop (Right a))
                        , onDragStartWithOptions preventDefault Nop
                        , value_ ruleTxt
                        ]
                    ]
                | hasRule
                ]
          )
      ]
        ++ if not parseSuccessFormula then [viewErrorIcon err] else ([viewErrorIcon ruleErr | hasRule && not parseSuccessRule])
    )
 where
  (parseSuccessFormula, txt, err, hasRule, parseSuccessRule, ruleTxt, ruleErr) = case e of
    Left a -> case a of
      Parsed str a' -> (True, ms str, "", False, True, "", "")
      Unparsed str err -> (False, ms str, ms err, False, True, "", "")
    Right (Derivation f r) -> case (f, r) of
      (Parsed str f', Parsed str' r') -> (True, ms str, "", True, True, ms str', "")
      (Parsed str f', Unparsed str' err') -> (True, ms str, "", True, False, ms str', ms err')
      (Unparsed str err, Parsed str' r') -> (False, ms str, ms err, True, True, ms str', "")
      (Unparsed str err, Unparsed str' err') -> (False, ms str, ms err, True, False, ms str', ms err')

viewProof :: Model -> View Model Action
viewProof model = H.div_ [] [proofView]
 where
  proofView = case model ^. proof of
    ProofLine _ -> error "Tried calling viewProof on a ProofLine"
    SubProof fs ps d -> H.div_ [HP.class_ "outer-subproof", HP.intProp "data-lines" (lLength (model ^. proof))] (viewAssumptions ++ viewProofs ++ [viewConclusion])
     where
      (_, viewAssumptions) = L.mapAccumL (\n f -> (n + 1, viewLine model n (NAAssumption n) (n == L.length fs - 1) (Left f))) 0 fs
      (n, viewProofs) = L.mapAccumL (\n p -> (n + 1, _viewProof n Nothing p)) 0 ps
      viewConclusion = viewLine model n NAConclusion False (Right d)
  _viewProof :: Int -> Maybe NodeAddr -> Proof -> View Model Action
  _viewProof n Nothing (ProofLine d) = viewLine model n (NAProof n Nothing) False (Right d)
  _viewProof n (Just a) (ProofLine d) = viewLine model n (naAppendProof n a) False (Right d)
  _viewProof n ma (SubProof fs ps d) =
    H.div_
      [ HP.class_ "subproof"
      , HP.draggable_ True
      , HP.hidden_ False
      , -- , HP.intProp "data-lines" (lLength $ SubProof fs ps d)
        HP.styleInline_ $ ms $ "grid-row: span " ++ show (lLength $ SubProof fs ps d)
      , onDragStartWithOptions stopPropagation $ DragStart a
      , onDragEndWithOptions stopPropagation DragEnd
      ]
      (viewAssumptions ++ viewProofs ++ [viewConclusion])
   where
    a = case ma of
      Nothing -> NAProof n Nothing
      Just addr -> naAppendProof n addr
    (_, viewAssumptions) = L.mapAccumL (\m f -> (m + 1, viewLine model m (naAppendAssumption m a) (m == L.length fs - 1) (Left f))) 0 fs
    (m, viewProofs) = L.mapAccumL (\m p -> (m + 1, _viewProof m (Just a) p)) 0 ps
    viewConclusion = viewLine model m (naAppendConclusion a) False (Right d)

-----------------------------------------------------------------------------
toEm :: Int -> MisoString
toEm n = ms (show n ++ "em")