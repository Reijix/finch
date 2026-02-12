module Util where

import Miso.Types

{- | Returns all combinations of a list of list.
Taken from package 'liquid-fixpoint' and adjusted to use `NonEmpty`.

Satisfies:
@allCombinations :: xss:[[a]] -> [{v:[a]| len v == len xss}]@
-}
allCombinations :: [NonEmpty a] -> NonEmpty [a]
allCombinations xs = assert (all ((length xs ==) . length)) $ go xs
 where
  go [] = [[]]
  go ((x :| []) : ys) = (x :) <$> go ys
  go ((x :| (x' : xs')) : ys) = ((x :) <$> go ys) <> go ((x' :| xs') : ys)

  assert b x = if b x then x else error "allCombinations: assertion violation"

interleave :: [a] -> [a] -> [a]
interleave [] _ = []
interleave (x : _) [] = [x]
interleave (x : xs) (y : ys) = x : y : interleave xs ys

-- addClass :: MisoString -> View model action -> View model action
-- addClass cls views = case views of
--   (VNode ns ms attrs views) ->
--     case updateClass attrs of
--       (True, attrs') -> VNode ns ms attrs' views
--       (False, _) -> VNode ns ms (ClassList (one cls) : attrs) views
--   (VComp attrs comp) ->
--     case updateClass attrs of
--       (True, attrs') -> VComp attrs' comp
--       (False, _) -> VComp (ClassList (one cls) : attrs) comp
--   txt -> txt
--  where
--   updateClass :: [Attribute action] -> (Bool, [Attribute action])
--   updateClass (ClassList classes : rest) = (True, ClassList (cls : classes) : rest)
--   updateClass (_ : rest) = updateClass rest
--   updateClass [] = (False, [])