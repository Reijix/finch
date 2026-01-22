module Parser.Rule where

import Control.Monad (liftM2, liftM3)
import Control.Monad.Combinators.Expr (
  Operator (InfixL, Prefix),
  makeExprParser,
 )
import Data.Char (digitToInt)
import Data.Text (Text, pack, unpack)
import Data.Text qualified as T
import Data.Void
import Fitch.Proof
import Parser.Prelude
import Text.Megaparsec
import Text.Megaparsec.Char (digitChar, letterChar, printChar, space1, string)
import Text.Megaparsec.Char.Lexer qualified as L

pLine :: (Parser m) => m Int
pLine = lexeme L.decimal <?> "line number"

pReference :: (Parser m) => m Reference
pReference = proofReference <|> lineReference
 where
  proofReference = liftM2 ProofReference (try $ pLine <* lexeme minus) pLine <?> "line range"
  lineReference = LineReference <$> pLine <?> "line number"

pRule :: (Parser m) => m RuleApplication
pRule = liftM2 RuleApplication (parens pSymbolicName) (lexeme pReference `sepBy` comma)

parseRuleApplication :: Int -> Text -> Either Text RuleApplication
parseRuleApplication lineNo input = case runParser' (pRule <* eof) initialParserState of
  (_, Left e) -> Left . pack $ errorBundlePretty e
  (_, Right ra) -> Right ra
 where
  initialParserState =
    State
      { stateInput = input
      , stateOffset = 0
      , statePosState =
          PosState
            { pstateInput = input
            , pstateOffset = 0
            , pstateSourcePos = SourcePos{sourceName = "", sourceLine = mkPos lineNo, sourceColumn = pos1}
            , pstateTabWidth = defaultTabWidth
            , pstateLinePrefix = ""
            }
      , stateParseErrors = []
      }
