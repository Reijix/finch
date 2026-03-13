{- |
Module      : App.Entry
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This is the entry point of the Finch application. It reads the @?logic=@
and @?proof=@ URL query parameters to select the initial logic (propositional
or first-order) and to optionally restore a t'Proof' encoded in the URL,
then starts the Miso application with the appropriate t'Model'.
-}
module App.Entry where

import App.Model
import App.URLDecoder
import App.Update
import App.Views
import Data.Text qualified as T
import Fitch.Proof
import Miso
import Miso.Subscription.Util (createSub)
import Relude.Extra.Map
import Specification.FOL
import Specification.Prop

------------------------------------------------------------------------------------------

-- * Running the App

{- | Starts the Miso application for the given @window@ t'DOMRef' and
initial t'Model'.

Registers the browser event listeners (drag, keyboard, mouse,
touch and default events), mounts the application with the 'Setup' action,
and adds the 'PopState' URI subscription together with the keyboard
subscription 'onKeyDownSub'.
-}
startAppWrapper :: DOMRef -> Model -> IO ()
startAppWrapper window model =
  startApp
    ( dragEvents
        <> fromList [("dblclick", BUBBLE)]
        <> keyboardEvents
        <> defaultEvents
        <> mouseEvents
        <> touchEvents
    )
    $ (component model updateModel viewModel)
      { mount = Just Setup
      , subs = [uriSub PopState, onKeyDownSub window]
      }

{- | Application entry point.

1. Reads the current t'URI'.
2. Inspects the @?logic=@ query parameter:

   * @prop@ — initializes propositional logic via 'initialModelProp'.
   * @fol@ — initializes first-order logic via 'initialModelFOL'.
   * defaults to @fol@.
3. If a @?proof=@ query parameter is present, decodes it with
   'decodeFromUrl' and uses it as the initial t'Proof'; otherwise the
   default example proof for the selected logic is shown.
4. Then starts the Miso application using 'startAppWrapper'.
-}
runApp :: IO ()
runApp = do
  window <- jsg "window"
  url <- getURI
  model <- case uriQueryString url !? "logic" of
    Just (Just "prop") ->
      pure $
        initialModelProp url $
          decodeFromUrl . show =<< join (uriQueryString url !? "proof")
    Just (Just "fol") ->
      pure $
        initialModelFOL url $
          decodeFromUrl . show
            =<< join
              (uriQueryString url !? "proof")
    _ -> do
      pure $
        initialModelFOL url $
          decodeFromUrl . show
            =<< join
              (uriQueryString url !? "proof")
  startAppWrapper window model

------------------------------------------------------------------------------------------

-- * Subscriptions

{- | Subscription for the @onkeydown@ event.

Used for detecting presses of @(@ and @Enter@.

* On @Enter@ fires the `Blur` event,
* On @(@ inserts the closing parenthesis at the end of selection.
-}
onKeyDownSub :: DOMRef -> Sub Action
onKeyDownSub window = createSub acquire (removeEventListener window "keydown")
 where
  acquire = do
    addEventListener window "keydown" $ \evt -> do
      domRef <- jsg "document" # "querySelector" $ (".focused" :: MisoString)
      isNull domRef >>= \case
        True -> pass
        False -> do
          Just (keyCode :: Int) <- castJSVal =<< getProperty evt "keyCode"
          Just (shiftKey :: Bool) <- castJSVal =<< getProperty evt "shiftKey"
          Just (start :: Int) <- castJSVal =<< getProperty domRef "selectionStart"
          Just (end :: Int) <- castJSVal =<< getProperty domRef "selectionEnd"

          -- when '(' is pressed, insert closing parenthesis as well
          when (keyCode == 57 && shiftKey && start < end) $ void $ do
            -- prevent call of the `input` event.
            eventPreventDefault evt
            -- split current value into parts, to insert the parentheses
            Just (value :: Text) <- castJSVal =<< getProperty domRef "value"
            let (firstPart, rest) = T.splitAt start value
                (secondPart, third) = T.splitAt (end - start) rest
                newTxt = T.concat [firstPart, "(", secondPart, ")", third]
            -- select all text, replace it with the new text, and adjust cursor position
            doc <- jsg "document"
            _ <- domRef # "select" $ ()
            -- NOTE: execCommand is deprecated, however its use is still recommended
            --       for inserting text to <input> while keeping the history intact.
            _ <- doc # "execCommand" $ ("insertText" :: String, False, newTxt)
            domRef # "setSelectionRange" $ (end + 2, end + 2, "none" :: String)

          -- when 'Enter' is pressed, call blur on the element, to lose focus
          when (keyCode == 13) $ void $ callFunction domRef "blur" ()

------------------------------------------------------------------------------------------
