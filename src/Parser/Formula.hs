module Parser.Formula (parseFormula, parseTestT, pFormula) where

import Control.Monad
import Control.Monad.Combinators.Expr
import Control.Monad.State
import Fitch.Proof
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

data FormulaParserState = FormulaParserState
  { functionSymbols :: [(String, Int)],
    predicateSymbols :: [(String, Int)],
    unaryOperators :: [String],
    binaryOperators :: [String],
    quantifiers :: [String],
    firstOrder :: Bool
  }

-- TODO work on error printing
instance ShowErrorComponent String where
  showErrorComponent :: String -> String
  showErrorComponent = id

type FormulaParser = ParsecT String String (State FormulaParserState)

sc :: FormulaParser ()
sc =
  L.space
    space1 -- discard spaces
    empty -- no line comments
    empty -- no block comments

lexeme :: FormulaParser a -> FormulaParser a
lexeme = L.lexeme sc

symbol :: String -> FormulaParser String
symbol = L.symbol sc

pName :: FormulaParser Name
pName = lexeme (some letterChar <?> "name")

comma :: FormulaParser String
comma = symbol ","

pFunName :: FormulaParser Name
pFunName = do
  symbols <- gets functionSymbols
  foldr (\(smb, _) p -> chunk smb <|> p) empty symbols

pFun :: FormulaParser Term
pFun = lexeme $ liftM2 Fun pFunName (parens (pTerm `sepBy` comma))

pVar :: FormulaParser Term
pVar = Var <$> lexeme (some letterChar <?> "variable")

parens :: FormulaParser a -> FormulaParser a
parens = between (symbol "(") (symbol ")")

pTermAtomic :: FormulaParser Term
pTermAtomic = choice [try pFun, pVar]

pTerm :: FormulaParser Term
pTerm = makeExprParser pTermAtomic []

pPredicateName :: FormulaParser Name
pPredicateName = do
  symbols <- gets predicateSymbols
  foldr (\(smb, _) p -> chunk smb <|> p) empty symbols

pPredicate :: FormulaParser Formula
pPredicate = lexeme $ liftM2 Predicate pPredicateName (parens (pTerm `sepBy` comma))

pPropAtom :: FormulaParser Formula
pPropAtom = lexeme $ (`Predicate` []) <$> pName

pQuantifierName :: FormulaParser Name
pQuantifierName = do
  symbols <- gets quantifiers
  foldr (\s p -> chunk s <|> p) empty symbols

pQuantifier :: FormulaParser Formula
pQuantifier = lexeme $ liftM3 Quantifier (lexeme pQuantifierName) (lexeme pName) (lexeme (string ".") >> pFormula)

pFormulaAtomic :: FormulaParser Formula
pFormulaAtomic =
  gets firstOrder >>= \case
    True -> choice [try pQuantifier, try pPredicate, parens pFormula]
    False -> choice [try pPropAtom, parens pFormula]

binary :: String -> (a -> a -> a) -> Operator FormulaParser a
binary name f = InfixL (f <$ symbol name)

prefix, postfix :: String -> (a -> a) -> Operator FormulaParser a
prefix name f = Prefix (f <$ symbol name)
postfix name f = Postfix (f <$ symbol name)

pFormula :: FormulaParser Formula
pFormula = do
  unaries <- gets unaryOperators
  binaries <- gets binaryOperators
  let operatorTable =
        [ map (\u -> prefix u (UnaryOp u)) unaries,
          map (\b -> binary b (BinaryOp b)) binaries
        ]
   in makeExprParser pFormulaAtomic operatorTable

parseFormula :: [(String, Int)] -> [(String, Int)] -> [String] -> [String] -> [String] -> Bool -> String -> Either String Formula
parseFormula functionSymbols predicateSymbols unaryOperators binaryOperators quantifiers firstOrder input = case evalState (runParserT (pFormula <* eof) "" input) initialState of
  Left e -> Left "error"
  Right f -> Right f
  where
    initialState =
      FormulaParserState
        { functionSymbols,
          predicateSymbols,
          unaryOperators,
          binaryOperators,
          quantifiers,
          firstOrder
        }

parseTestT :: (Show a) => ParsecT String String (State FormulaParserState) a -> String -> IO ()
parseTestT p input = case evalState (runParserT p "" input) (FormulaParserState {functionSymbols = [("f", 1)], predicateSymbols = [("P", 1)], unaryOperators = ["~"], binaryOperators = ["/\\", "\\/", "->"], quantifiers = ["forall"], firstOrder = True}) of
  Left e -> putStr $ errorBundlePretty e
  Right x -> print x
