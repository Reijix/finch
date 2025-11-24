module Parser.Formula where

import Parser.Lexer
import Text.Megaparsec

data Operator = NaryOp Int String | Quantifier String

formulaParser :: (formula -> Operator) -> Parser formula
formulaParser = _