module FitchTest where

import Data.Text (Text, pack)
import Data.Text.IO
import Fitch.Proof (prettyProof)
import Parser.Formula (parseFormula)
import Parser.Proof
import System.IO (IOMode (..), openFile)

-- import System.IO

infixPreds :: [(Text, Text)]
infixPreds = [("", "=")]
operators :: [(Text, Text, Int)]
operators = [("false", "⊥", 0), ("true", "⊤", 0), ("~", "¬", 1), ("/\\", "∧", 2), ("\\/", "∨", 2), ("->", "→", 2)]
quantifiers :: [(Text, Text)]
quantifiers = [("forall", "∀"), ("exists", "∃")]

main :: IO ()
main = do
  handle <- openFile "tests/Examples/Proof1.fitch" ReadMode
  contents <- hGetContents handle
  case parseProof operators infixPreds quantifiers contents of
    Left err -> Data.Text.IO.putStrLn err
    Right p -> Data.Text.IO.putStrLn $ prettyProof p