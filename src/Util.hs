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

{- | `insertAt` @x@ @n@ @xs@ inserts @x@ at index @n@ into @xs@.

Fails for @n < 0@, returns @xs@ for @n > length xs@.
-}
insertAt :: a -> Int -> [a] -> [a]
insertAt x 0 xs = x : xs
insertAt x n [] = [x]
insertAt x n (y : ys) = y : insertAt x (n - 1) ys

{- | `removeAt` @n@ @xs@ removes the element at index @n@.

Returns @xs@ for invalid indices.
-}
removeAt :: Int -> [a] -> [a]
removeAt n [] = []
removeAt n (x : xs)
  | n < 0 = x : xs
  | n == 0 = xs
  | n > 0 = x : removeAt (n - 1) xs

{- | Update nth element of a list, if it exists.
  @O(min index n)@.

  Precondition: the index is >= 0.
  (Copied from Agda.Utils.List)
-}
updateAt :: Int -> (a -> a) -> [a] -> [a]
updateAt _ _ [] = []
updateAt 0 f (a : as) = f a : as
updateAt n f (a : as) = a : updateAt (n - 1) f as