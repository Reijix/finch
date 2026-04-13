{- |
Module      : Util
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

Some utility functions.
-}
module Util where

import Miso.Lens (Lens, (%=))

------------------------------------------------------------------------------------------

-- * List utilities

{- | Returns all combinations of a list of list.
Taken from package
[liquid-fixpoint](https://hackage.haskell.org/package/liquid-fixpoint-0.5.0.1)
and adjusted to use `NonEmpty`.

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

{- | Interleaves two lists, taking elements alternately from each.
The result ends when the first list is exhausted. If the second list
runs out first, the remaining head of the first list is appended.

>>> interleave [1,2,3] [10,20,30]
[1,10,2,20,3,30]
>>> interleave [1,2,3] [10]
[1,10,2]
-}
interleave :: [a] -> [a] -> [a]
interleave [] _ = []
interleave (x : _) [] = [x]
interleave (x : xs) (y : ys) = x : y : interleave xs ys

{- | `insertAt` @x@ @n@ @xs@ inserts @x@ at index @n@ into @xs@.
Returns v'Nothing' for invalid indices.
-}
insertAt :: a -> Int -> [a] -> Maybe [a]
insertAt x 0 xs = Just $ x : xs
insertAt x n (y : ys) = (y :) <$> insertAt x (n - 1) ys
insertAt _ _ _ = Nothing

{- | `removeAt` @n@ @xs@ removes the element at index @n@.
Returns v'Nothing' for invalid indices.
-}
removeAt :: Int -> [a] -> Maybe [a]
removeAt n [] = Nothing
removeAt n (x : xs)
  | n < 0 = Just $ x : xs
  | n == 0 = Just xs
  | n > 0 = (x :) <$> removeAt (n - 1) xs

{- | Update nth element of a list, if it exists.
  @O(min index n)@.

  Precondition: the index is >= 0.
  (Copied from Agda.Utils.List and adjusted for monadicity)
-}
updateAtM :: (MonadFail m) => Int -> (a -> m a) -> [a] -> m [a]
updateAtM _ _ [] = fail ""
updateAtM 0 f (a : as) = f a <&> (: as)
updateAtM n f (a : as) = (a :) <$> updateAtM (n - 1) f as

------------------------------------------------------------------------------------------

-- * Lens utilities

{- | A variant of '(%=)' that only updates the field when the function
returns 'Just'. If the function returns 'Nothing', the field is left
unchanged.
-}
(%=?) :: (MonadState record m) => Lens record field -> (field -> Maybe field) -> m ()
(%=?) _lens f = _lens %= (\x -> fromMaybe x (f x))

------------------------------------------------------------------------------------------

-- * Numeric utilities

-- | Returns whether the given integer lies inside the inclusive interval.
inRange :: (Int, Int) -> Int -> Bool
inRange (start, end) n = n >= start && n <= end

-- | Turns text into plural (by appending \'s\') when the second argument is not 1.
plural :: Text -> Int -> Text
plural txt 1 = txt
plural txt n = txt <> "s"
