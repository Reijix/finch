module Util where

import Miso.Lens (Lens, (%=))

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

-- | `insertAt` @x@ @n@ @xs@ inserts @x@ at index @n@ into @xs@.
insertAt :: a -> Int -> [a] -> Maybe [a]
insertAt x 0 xs = Just $ x : xs
insertAt x n (y : ys) = (y :) <$> insertAt x (n - 1) ys
insertAt _ _ _ = Nothing

-- | `removeAt` @n@ @xs@ removes the element at index @n@.
removeAt :: Int -> [a] -> Maybe [a]
removeAt n [] = Nothing
removeAt n (x : xs)
  | n < 0 = Just $ x : xs
  | n == 0 = Just xs
  | n > 0 = (x :) <$> removeAt (n - 1) xs

{- | Update nth element of a list, if it exists.
  @O(min index n)@.

  Precondition: the index is >= 0.
  (Copied from Agda.Utils.List)
-}
updateAtM :: (MonadFail m) => Int -> (a -> m a) -> [a] -> m [a]
updateAtM _ _ [] = fail ""
updateAtM 0 f (a : as) = f a <&> (: as)
updateAtM n f (a : as) = (a :) <$> updateAtM (n - 1) f as

(%=?) :: (MonadState record m) => Lens record field -> (field -> Maybe field) -> m ()
(%=?) _lens f = _lens %= (\x -> fromMaybe x (f x))
