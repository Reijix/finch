{- |
Module      : Parser.Rule
Copyright   : (c) Leon Vatthauer, 2026
License     : GPL-3
Maintainer  : Leon Vatthauer <leon.vatthauer@fau.de>
Stability   : experimental
Portability : non-portable (ghc-wasm-meta)

This module defines parsers for t'RuleApplication's and t'Reference's.
-}
module Parser.Rule where

import Control.Monad.Combinators.Expr (
  Operator (InfixL, Prefix),
  makeExprParser,
 )
import Fitch.Proof
import Parser.Util
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

-----------------------------------------------------------------------------

-- * Parsers

-- | Parses a positive integer as a line number.
pLine :: (Parser m) => m Int
pLine = lexeme L.decimal <?> "line number"

{- | Parses a t'Reference': either a v'ProofReference' (a line range @m-n@)
or a v'LineReference' (a single line number @n@).
-}
pReference :: (Parser m) => m Reference
pReference = proofReference <|> lineReference
 where
  proofReference = liftA2 ProofReference (try $ pLine <* lexeme minus) pLine <?> "line range"
  lineReference = LineReference <$> pLine <?> "line number"

{- | Parses a t'RuleApplication': a rule name enclosed in parentheses,
followed by a comma-separated list of t'Reference's.
-}
pRule :: (Parser m) => m RuleApplication
pRule =
  liftA2
    RuleApplication
    (parens (try pSymbolicName <|> pure ""))
    (lexeme pReference `sepBy` comma)

-----------------------------------------------------------------------------

-- * Entry point

{- | Parses a t'RuleApplication' from a t'Text'.
Returns 'Left' with a human-readable error message on failure,
or 'Right' with the parsed t'RuleApplication' on success.
-}
parseRuleApplication ::
  -- | Line number, used to anchor error positions.
  Int ->
  -- | Input t'Text' to parse.
  Text ->
  Either Text RuleApplication
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
            , pstateSourcePos =
                SourcePos{sourceName = "", sourceLine = mkPos lineNo, sourceColumn = pos1}
            , pstateTabWidth = defaultTabWidth
            , pstateLinePrefix = ""
            }
      , stateParseErrors = []
      }
