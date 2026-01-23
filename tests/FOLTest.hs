module FOLTest where

import Data.Map (Map)
import Data.Map qualified as M
import Data.Text (Text, pack)
import Data.Text.IO
import Fitch.Proof
import Parser.Formula (parseFormula)
import Parser.Proof
import Specification.FOL
import System.IO (IOMode (..), openFile)
import Test.Tasty
import Test.Tasty.HUnit

readProof :: String -> IO (Either Text Proof)
readProof filePath = do
  handle <- openFile filePath ReadMode
  contents <- hGetContents handle
  case parseProof operatorsFOL infixPredsFOL quantifiersFOL contents of
    Left err -> return $ Left err
    Right p -> return $ Right p

main :: IO ()
main = undefined