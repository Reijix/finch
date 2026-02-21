module Parser.Rule where

import Control.Monad.Combinators.Expr (
  Operator (InfixL, Prefix),
  makeExprParser,
 )
import Fitch.Proof (Reference (..), RuleApplication (..))
import Parser.Util (
  Parser,
  comma,
  lexeme,
  minus,
  pSymbolicName,
  parens,
 )
import Text.Megaparsec (
  MonadParsec (eof, try),
  PosState (
    PosState,
    pstateInput,
    pstateLinePrefix,
    pstateOffset,
    pstateSourcePos,
    pstateTabWidth
  ),
  SourcePos (SourcePos, sourceColumn, sourceLine, sourceName),
  State (
    State,
    stateInput,
    stateOffset,
    stateParseErrors,
    statePosState
  ),
  defaultTabWidth,
  errorBundlePretty,
  mkPos,
  pos1,
  runParser',
  sepBy,
  (<?>),
 )
import Text.Megaparsec.Char (digitChar, letterChar, printChar, space1, string)
import Text.Megaparsec.Char.Lexer qualified as L

pLine :: (Parser m) => m Int
pLine = lexeme L.decimal <?> "line number"

pReference :: (Parser m) => m Reference
pReference = proofReference <|> lineReference
 where
  proofReference = liftA2 ProofReference (try $ pLine <* lexeme minus) pLine <?> "line range"
  lineReference = LineReference <$> pLine <?> "line number"

pRule :: (Parser m) => m RuleApplication
pRule = liftA2 RuleApplication (parens (try pSymbolicName <|> pure "")) (lexeme pReference `sepBy` comma)

parseRuleApplication :: Int -> Text -> Either Text RuleApplication
parseRuleApplication lineNo input = case runParser' (pRule <* eof) initialParserState of
  (_, Left e) -> Left . toText $ errorBundlePretty e
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
