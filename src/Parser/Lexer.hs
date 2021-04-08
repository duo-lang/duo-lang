module Parser.Lexer
  ( sc
  , numP
    -- Names
  , freeVarName
  , xtorName
  , typeNameP
    -- Keywords
  , matchKwP
  , comatchKwP
  , prdKwP
  , cnsKwP
  , cmdKwP
  , defKwP
  , withKwP
  , doneKwP
  , printKwP
  , forallKwP
  , dataKwP
  , codataKwP
  , recKwP
  , muKwP
  , muStarKwP
    -- Symbols
  , dot
  , pipe
  , comma
  , semi
  , backslash
  , coloneq
  , rightarrow
  , commandSym
  , unionSym
  , intersectionSym
  , subtypeSym
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
-- General lexing conventions around space consumption and source code locations:
--
-- Every lexer and parser is responsible for consuming it's trailing whitespace using the
-- space consumer `sc`.
-- In addition, every parser returns the source position of the end of the last parsed
-- non-whitespace token.
--
-- Example:
-- A parser for number literals:
--
-- (This source position is returned)
--            ||
--            \/
--    123456789          foo
--    ^^^^^^^^^^^^^^^^^^^
--      (this is parsed)
--
-------------------------------------------------------------------------------------------

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "#") (L.skipBlockComment "###" "###")

-------------------------------------------------------------------------------------------
-- Helper functions
-------------------------------------------------------------------------------------------

symbol :: String -> Parser SourcePos
symbol str = do
  _ <- string str
  endPos <- getSourcePos
  sc
  return endPos

lexeme :: Parser a -> Parser (a, SourcePos)
lexeme p = do
  res <- p
  endPos <- getSourcePos
  sc
  return (res, endPos)


keywordP :: String -> Parser SourcePos
keywordP str = do
  _ <- string str <* notFollowedBy alphaNumChar
  endPos <- getSourcePos
  sc
  return endPos

numP :: Parser (Int, SourcePos)
numP = do
  (numStr, pos) <- lexeme (some numberChar)
  return (read numStr, pos)

-------------------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------------------

freeVarName :: Parser (FreeVarName, SourcePos)
freeVarName = do
  (name, pos) <- lexeme $ ((:) <$> lowerChar <*> many alphaNumChar)
  checkReserved name
  return (name, pos)


xtorName :: NominalStructural -> Parser (XtorName, SourcePos)
xtorName Structural = do
  _ <- tick
  (name, pos) <- lexeme $ (:) <$> upperChar <*> many alphaNumChar
  checkReserved name
  return (MkXtorName Structural name, pos) -- Saved without tick!
xtorName Nominal = do
  (name, pos) <- lexeme $ (:) <$> upperChar <*> many alphaNumChar
  checkReserved name
  return (MkXtorName Nominal name, pos)

typeNameP :: Parser (TypeName, SourcePos)
typeNameP = do
  (name, pos) <- lexeme $ (:) <$> upperChar <*> many alphaNumChar
  checkReserved name
  return (MkTypeName name, pos)

-------------------------------------------------------------------------------------------
-- Keywords
-------------------------------------------------------------------------------------------

keywords :: [String]
keywords = ["match", "comatch", "prd", "cns", "cmd", "def", "with"
           , "Done", "Print", "forall", "data", "codata", "rec", "mu", "mu*"]

-- Check if the string is in the list of reserved keywords.
-- Reserved keywords cannot be used as identifiers.
checkReserved :: String -> Parser ()
checkReserved str | str `elem` keywords = fail $ "Keyword " <> str <> " cannot be used as an identifier."
                  | otherwise = return ()

matchKwP :: Parser SourcePos
matchKwP = keywordP "match"

comatchKwP :: Parser SourcePos
comatchKwP = keywordP "comatch"

prdKwP :: Parser SourcePos
prdKwP = keywordP "prd"

cnsKwP :: Parser SourcePos
cnsKwP = keywordP "cns"

cmdKwP :: Parser SourcePos
cmdKwP = keywordP "cmd"

defKwP :: Parser SourcePos
defKwP = keywordP "def"

withKwP :: Parser SourcePos
withKwP = keywordP "with"

doneKwP :: Parser SourcePos
doneKwP = keywordP "Done"

printKwP :: Parser SourcePos
printKwP = keywordP "Print"

forallKwP :: Parser SourcePos
forallKwP = keywordP "forall"

dataKwP :: Parser SourcePos
dataKwP = keywordP "data"

codataKwP :: Parser SourcePos
codataKwP = keywordP "codata"

recKwP :: Parser SourcePos
recKwP = keywordP "rec"

muKwP :: Parser SourcePos
muKwP = keywordP "mu"

muStarKwP :: Parser SourcePos
muStarKwP = keywordP "mu*"

-------------------------------------------------------------------------------------------
-- Symbols
-------------------------------------------------------------------------------------------

comma :: Parser SourcePos
comma = symbol ","

dot :: Parser SourcePos
dot = symbol "."

semi :: Parser SourcePos
semi = symbol ";"

pipe :: Parser SourcePos
pipe = symbol "|"

tick :: Parser SourcePos
tick = symbol "'"

backslash :: Parser SourcePos
backslash = symbol "\\"

coloneq :: Parser SourcePos
coloneq = symbol ":="

rightarrow :: Parser SourcePos
rightarrow = symbol "=>"

commandSym :: Parser SourcePos
commandSym = symbol ">>"

unionSym :: Parser SourcePos
unionSym = symbol "\\/"

intersectionSym :: Parser SourcePos
intersectionSym = symbol "/\\"

subtypeSym :: Parser SourcePos
subtypeSym = symbol "<:"

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

