module Util where

import Control.Monad.State
import Data.Maybe
import Miso.Lens

(%=?) :: (MonadState record m) => Lens record field -> (field -> Maybe field) -> m ()
(%=?) _lens f = _lens %= (\x -> fromMaybe x (f x))