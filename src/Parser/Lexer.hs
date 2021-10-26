module Parser.Lexer
  ( sc
  , numP
    -- Names
  , freeVarName
  , xtorName
  , typeNameP
  , moduleNameP
  , optionP
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
  , importKwP
  , setKwP
  , topKwP
  , botKwP
    -- Symbols
  , dot
  , pipe
  , comma
  , semi
  , colon
  , backslash
  , coloneq
  , rightarrow
  , commandSym
  , unionSym
  , intersectionSym
  , subtypeSym
  , refineSym
    -- Parens
  , angles
  , parens
  , brackets
  , braces
  , dbraces
  , argListP

  , checkTick
  , parseUntilKeywP
  ) where

import Data.Text (Text)
import qualified Data.Text as T
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import Parser.Definition
import Syntax.CommonTerm
import Syntax.Program
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

symbol :: Text -> Parser SourcePos
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


keywordP :: Text -> Parser SourcePos
keywordP str = do
  _ <- string str <* notFollowedBy alphaNumChar
  endPos <- getSourcePos
  sc
  return endPos

numP :: Parser (Int, SourcePos)
numP = do
  (numStr, pos) <- lexeme (some numberChar)
  return (read numStr, pos)

-- | Used for parsing options using the "set option;" syntax
optionP :: Parser (Text, SourcePos)
optionP = lexeme $ (T.cons <$> lowerChar <*> (T.pack <$> many alphaNumChar))

-------------------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------------------

freeVarName :: Parser (FreeVarName, SourcePos)
freeVarName = try $ do
  (name, pos) <- lexeme $ (T.cons <$> lowerChar <*> (T.pack <$> many alphaNumChar))
  checkReserved name
  return (name, pos)

checkTick :: NominalStructural -> Parser ()
checkTick Nominal = return ()
checkTick Structural = () <$ tick

xtorName :: NominalStructural -> Parser (XtorName, SourcePos)
xtorName ns = try $ do
  () <- checkTick ns
  (name, pos) <- lexeme $ T.cons <$> upperChar <*> (T.pack <$> many alphaNumChar)
  checkReserved name
  return (MkXtorName ns name, pos)

typeNameP :: Parser (TypeName, SourcePos)
typeNameP = try $ do
  (name, pos) <- lexeme $ T.cons <$> upperChar <*> (T.pack <$> many alphaNumChar)
  checkReserved name
  return (MkTypeName name, pos)

moduleNameP :: Parser (ModuleName, SourcePos)
moduleNameP = try $ do
  (name, pos) <- lexeme $ T.cons <$> upperChar <*> (T.pack <$> many alphaNumChar)
  checkReserved name
  return (ModuleName name, pos)

-------------------------------------------------------------------------------------------
-- Keywords
-------------------------------------------------------------------------------------------

keywords :: [Text]
keywords = ["match", "comatch", "prd", "cns", "cmd", "def", "with", "set", "Top", "Bot"
           , "Done", "Print", "forall", "data", "codata", "rec", "mu", "import"]

-- Check if the string is in the list of reserved keywords.
-- Reserved keywords cannot be used as identifiers.
checkReserved :: Text -> Parser ()
checkReserved str | str `elem` keywords = fail . T.unpack $ "Keyword " <> str <> " cannot be used as an identifier."
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

importKwP :: Parser SourcePos 
importKwP = keywordP "import"

setKwP :: Parser SourcePos 
setKwP = keywordP "set"

topKwP :: Parser SourcePos 
topKwP = keywordP "Top"

botKwP :: Parser SourcePos 
botKwP = keywordP "Bot"


-------------------------------------------------------------------------------------------
-- Symbols
-------------------------------------------------------------------------------------------

comma :: Parser SourcePos
comma = symbol ","

dot :: Parser SourcePos
dot = symbol "."

semi :: Parser SourcePos
semi = symbol ";"

colon :: Parser SourcePos
colon = symbol ":"

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

refineSym :: Parser SourcePos
refineSym = symbol "<<:"

-------------------------------------------------------------------------------------------
-- Parens
-------------------------------------------------------------------------------------------

betweenP :: Parser SourcePos -> Parser SourcePos -> Parser a -> Parser (a, SourcePos)
betweenP open close middle = do
  _ <- open
  res <- middle
  endPos <- close
  pure (res, endPos)

parens, braces, brackets, angles, dbraces :: Parser a -> Parser (a, SourcePos)
parens    = betweenP (symbol "(")  (symbol ")")
braces    = betweenP (symbol "{")  (symbol "}")
brackets  = betweenP (symbol "[")  (symbol "]")
angles    = betweenP (symbol "<")  (symbol ">")
dbraces   = betweenP (symbol "{{") (symbol "}}")

-- | Parse two lists, the first in parentheses and the second in brackets.
argListP ::  Parser a -> Parser a ->  Parser (Twice [a], SourcePos)
argListP p q = do
  endPos <- getSourcePos
  (xs, endPos) <- option ([], endPos) (parens   $ p `sepBy` comma)
  (ys, endPos) <- option ([], endPos) (brackets $ q `sepBy` comma)
  return (Twice xs ys, endPos)

-------------------------------------------------------------------------------------------
-- Recovery parser
-------------------------------------------------------------------------------------------

parseUntilKeywP :: Parser ()
parseUntilKeywP = do
  let endP = prdKwP <|> cnsKwP <|> cmdKwP <|> defKwP <|> dataKwP <|> codataKwP <|> setKwP <|> (eof >> getSourcePos)
  _ <- manyTill anySingle (lookAhead endP)
  return ()

