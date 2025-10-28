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