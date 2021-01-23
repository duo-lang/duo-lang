module Parser.Lexer where

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L
import Utils

import Parser.Definition
import Syntax.Terms
-------------------------------------------------------------------------------------------
-- Lexer
-------------------------------------------------------------------------------------------

sepBy2 :: Parser a -> Parser sep -> Parser [a]
sepBy2 p sep = (:) <$> (p <* sep) <*> (sepBy1 p sep)

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "#") (L.skipBlockComment "###" "###")

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

freeVarName :: Parser FreeVarName
freeVarName = lexeme $ ((:) <$> lowerChar <*> many alphaNumChar) <|> symbol "_"

xtorName :: NominalStructural -> Parser XtorName
xtorName Structural = do
  _ <- tick
  name <- (lexeme $ (:) <$> upperChar <*> many alphaNumChar)
  return (MkXtorName Structural name) -- Saved without tick!
xtorName Nominal = do
  name <- (lexeme $ (:) <$> upperChar <*> many alphaNumChar)
  return (MkXtorName Nominal name)

typeIdentifierName :: Parser String
typeIdentifierName = lexeme $ (:) <$> upperChar <*> many alphaNumChar

parens, braces, brackets, angles :: Parser a -> Parser a
parens    = between (symbol "(") (symbol ")")
braces    = between (symbol "{") (symbol "}")
brackets  = between (symbol "[") (symbol "]")
angles    = between (symbol "<") (symbol ">")

comma, dot, pipe, tick :: Parser String
comma = symbol ","
dot = symbol "."
pipe = symbol "|"
tick = symbol "'"

-- | Parse two lists, the first in parentheses and the second in brackets.
argListP ::  Parser a -> Parser a ->  Parser (Twice [a])
argListP p q = do
  xs <- option [] (parens   $ p `sepBy` comma)
  ys <- option [] (brackets $ q `sepBy` comma)
  return $ Twice xs ys
