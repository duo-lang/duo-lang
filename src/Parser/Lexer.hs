module Parser.Lexer
  ( sc
  , sepBy2
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
-- Various
-------------------------------------------------------------------------------------------

symbol :: String -> Parser ()
symbol str = L.symbol sc str >> return ()

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

keywordP :: String -> Parser ()
keywordP str = lexeme (string str <* notFollowedBy alphaNumChar) >> return ()

sepBy2 :: Parser a -> Parser sep -> Parser [a]
sepBy2 p sep = (:) <$> (p <* sep) <*> (sepBy1 p sep)

sc :: Parser ()
sc = L.space space1 (L.skipLineComment "#") (L.skipBlockComment "###" "###")

numP :: Parser Int
numP = do
  numStr <- lexeme (some numberChar)
  return (read numStr)

-------------------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------------------

freeVarName :: Parser FreeVarName
freeVarName = lexeme $ ((:) <$> lowerChar <*> many alphaNumChar) 

xtorName :: NominalStructural -> Parser XtorName
xtorName Structural = do
  tick
  name <- (lexeme $ (:) <$> upperChar <*> many alphaNumChar)
  return (MkXtorName Structural name) -- Saved without tick!
xtorName Nominal = do
  name <- (lexeme $ (:) <$> upperChar <*> many alphaNumChar)
  return (MkXtorName Nominal name)

typeNameP :: Parser TypeName
typeNameP = MkTypeName <$> (lexeme $ (:) <$> upperChar <*> many alphaNumChar)

-------------------------------------------------------------------------------------------
-- Keywords
-------------------------------------------------------------------------------------------

keywords :: [String]
keywords = ["match", "comatch", "prd", "cns", "cmd", "def", "with", "Done", "Print", "forall", "data", "codata", "rec", "mu", "mu*"]

matchKwP :: Parser ()
matchKwP = keywordP "match"

comatchKwP :: Parser ()
comatchKwP = keywordP "comatch"

prdKwP :: Parser ()
prdKwP = keywordP "prd"

cnsKwP :: Parser ()
cnsKwP = keywordP "cns"

cmdKwP :: Parser ()
cmdKwP = keywordP "cmd"

defKwP :: Parser ()
defKwP = keywordP "def"

withKwP :: Parser ()
withKwP = keywordP "with"

doneKwP :: Parser ()
doneKwP = keywordP "Done"

printKwP :: Parser ()
printKwP = keywordP "Print"

forallKwP :: Parser ()
forallKwP = keywordP "forall"

dataKwP :: Parser ()
dataKwP = keywordP "data"

codataKwP :: Parser ()
codataKwP = keywordP "codata"

recKwP :: Parser ()
recKwP = keywordP "rec"

muKwP :: Parser ()
muKwP = keywordP "mu"

muStarKwP :: Parser ()
muStarKwP = keywordP "mu*"

-------------------------------------------------------------------------------------------
-- Symbols
-------------------------------------------------------------------------------------------

comma :: Parser ()
comma = symbol ","

dot :: Parser ()
dot = symbol "."

semi :: Parser ()
semi = symbol ";"

pipe :: Parser ()
pipe = symbol "|"

tick :: Parser ()
tick = symbol "'"

backslash :: Parser ()
backslash = symbol "\\"

coloneq :: Parser ()
coloneq = symbol ":="

rightarrow :: Parser ()
rightarrow = symbol "=>"

commandSym :: Parser ()
commandSym = symbol ">>"

unionSym :: Parser ()
unionSym = symbol "\\/"

intersectionSym :: Parser ()
intersectionSym = symbol "/\\"

subtypeSym :: Parser ()
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

