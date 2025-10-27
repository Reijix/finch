module Proof.Util where

insertAt :: a -> Int -> [a] -> Maybe [a]
insertAt x 0 xs = Just $ x : xs
insertAt x n [] = Nothing
insertAt x n (y : ys) = do
  ys' <- insertAt x (n - 1) ys
  Just $ y : ys'

removeAt :: Int -> [a] -> Maybe [a]
removeAt n [] = Nothing
removeAt n (x : xs)
  | n < 0 = Nothing
  | n == 0 = Just xs
  | n > 0 = do
      xs' <- removeAt (n - 1) xs
      return $ x : xs'