module Parser.Rule (parseRuleApplication) where

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
import Text.Megaparsec
import Text.Megaparsec.Char (digitChar, letterChar, printChar, space1, string)
import Text.Megaparsec.Char.Lexer qualified as L

type Parser = Parsec Void Text

sc :: Parser ()
sc =
  L.space
    space1 -- discard spaces
    empty -- no line comments
    empty -- no block comments

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: Text -> Parser Text
symbol = L.symbol sc

pName :: Parser Name
pName = lexeme (pack <$> some (noneOf ['(', ')']) <?> "name")

comma :: Parser Text
comma = symbol ","

minus :: Parser Text
minus = symbol "-"

pLine :: Parser Int
pLine = lexeme L.decimal <?> "line number"

parens :: Parser a -> Parser a
parens = between (symbol "(") (symbol ")")

pReference :: Parser Reference
pReference = proofReference <|> lineReference
 where
  proofReference = liftM2 ProofReference (try $ pLine <* lexeme minus) pLine <?> "line range"
  lineReference = LineReference <$> pLine <?> "line number"

pRule :: Parser RuleApplication
pRule = liftM2 RuleApplication (parens pName) (lexeme pReference `sepBy` comma)

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
