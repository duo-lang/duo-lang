module Parser.Lexer
  ( symbol
  , lexeme
  , sepBy2
  , sc
    -- Names
  , freeVarName
  , xtorName
  , typeNameP
    -- Punctuation
  , dot
  , pipe
  , comma
    -- Parens
  , angles
  , parens
  , brackets
  , braces
  , argListP
  ) where

import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Parser.Definition
import Syntax.CommonTerm
import Syntax.Types
import Utils

-------------------------------------------------------------------------------------------
-- Various
-------------------------------------------------------------------------------------------

symbol :: String -> Parser String
symbol = L.symbol sc

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

sepBy2 :: Parser a -> Parser sep -> Parser [a]
sepBy2 p sep = (:) <$> (p <* sep) <*> (sepBy1 p sep)

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "#") (L.skipBlockComment "###" "###")

-------------------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------------------

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

typeNameP :: Parser TypeName
typeNameP = MkTypeName <$> (lexeme $ (:) <$> upperChar <*> many alphaNumChar)

-------------------------------------------------------------------------------------------
-- Punctuation
-------------------------------------------------------------------------------------------

comma, dot, pipe, tick :: Parser String
comma = symbol ","
dot = symbol "."
pipe = symbol "|"
tick = symbol "'"

-------------------------------------------------------------------------------------------
-- Parens
-------------------------------------------------------------------------------------------

parens, braces, brackets, angles :: Parser a -> Parser a
parens    = between (symbol "(") (symbol ")")
braces    = between (symbol "{") (symbol "}")
brackets  = between (symbol "[") (symbol "]")
angles    = between (symbol "<") (symbol ">")

-- | Parse two lists, the first in parentheses and the second in brackets.
argListP ::  Parser a -> Parser a ->  Parser (Twice [a])
argListP p q = do
  xs <- option [] (parens   $ p `sepBy` comma)
  ys <- option [] (brackets $ q `sepBy` comma)
  return $ Twice xs ys

