module Proof.Util where

insertAt :: a -> Int -> [a] -> [a]
insertAt x 0 xs = x : xs
insertAt x n [] = []
insertAt x n (y : ys) = y : insertAt x (n - 1) ys

removeAt :: Int -> [a] -> [a]
removeAt n [] = []
removeAt n (x : xs)
  | n < 0 = x : xs
  | n == 0 = xs
  | n > 0 = x : removeAt (n - 1) xs

-- | Update nth element of a list, if it exists.
--   @O(min index n)@.
--
--   Precondition: the index is >= 0.
-- (Taken from Agda.Utils.List)
updateAt :: Int -> (a -> a) -> [a] -> [a]
updateAt _ _ [] = []
updateAt 0 f (a : as) = f a : as
updateAt n f (a : as) = a : updateAt (n - 1) f as