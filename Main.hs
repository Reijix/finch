{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OrPatterns #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import App.Decoder
import App.Model
import App.Update
import App.Views
import Data.Text qualified as T
import Miso
import Miso.Subscription.Util (createSub)
import Relude.Extra.Map
import Specification.FOL
import Specification.Prop

-----------------------------------------------------------------------------
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

main :: IO ()
main = do
  window <- jsg "window"
  uri <- getURI
  model <- case uriQueryString uri !? "logic" of
    Just (Just "prop") ->
      pure $ initialModelProp $ decodeFromUrl . show =<< join (uriQueryString uri !? "proof")
    Just (Just "fol") -> pure $ initialModelFOL $ decodeFromUrl . show =<< join (uriQueryString uri !? "proof")
    _ -> do
      -- TODO setURI!
      pure $ initialModelFOL $ decodeFromUrl . show =<< join (uriQueryString uri !? "proof")
  startAppWrapper window model

-----------------------------------------------------------------------------

-- * Subscriptions

{- | Subscription for the 'onkeydown' event.

Used for detecting presses of '(' and 'Enter'.
* On 'Enter' fires the `Blur` event,
* On '(' inserts the closing parenthesis at the end of selection.
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

-----------------------------------------------------------------------------
