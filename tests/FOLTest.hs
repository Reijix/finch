module FOLTest where

import Fitch.Proof
import Parser.Formula (parseFormula)
import Parser.Proof
import Specification.FOL
import Test.Tasty
import Test.Tasty.HUnit

readProof :: String -> IO (Either Text Proof)
readProof filePath = do
  contents <- readFileBS filePath
  pure $ parseProof operatorsFOL infixPredsFOL quantifiersFOL (decodeUtf8 contents)

main :: IO ()
main = do
  ep <- readProof "tests/Examples/Proof1.fitch"
  case ep of
    Left err -> putTextLn err
    Right p -> putTextLn $ prettyPrint p