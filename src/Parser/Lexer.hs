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
  , caseKwP
  , comatchKwP
  , cocaseKwP
  , ofKwP
  , prdKwP
  , cnsKwP
  , cmdKwP
  , doneKwP
  , printKwP
  , readKwP
  , forallKwP
  , dataKwP
  , codataKwP
  , infixlKwP
  , infixrKwP
  , recKwP
  , muKwP
  , importKwP
  , setKwP
  , topKwP
  , botKwP
  , cbvKwP
  , cbnKwP
  , typeKwP
    -- Symbols
  , varianceP
  , dot
  , pipe
  , comma
  , semi
  , colon
  , backslash
  , coloneq
  , rightarrow
  , thinRightarrow
  , commandSym
  , unionSym
  , intersectionSym
  , subtypeSym
  , refineSym
  , implicitSym
  , parSym
    -- Parens
  , angles
  , parens
  , brackets
  , braces
  , dbraces
  , parensListP
  , parensListIP
  , bracketsListP
  , bracketsListIP
  , argListsP
  , argListsIP
    -- Other
  , checkTick
  , parseUntilKeywP
  ) where

import Data.Text (Text)
import Data.Text qualified as T
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

import Parser.Definition
import Syntax.Common
import Syntax.AST.Types
import Syntax.Lowering.Types (Variance(..))

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
keywords = ["match", "comatch", "case", "cocase", "prd", "cns", "cmd", "of", "set", "Top", "Bot"
           , "Done", "Print", "Read", "forall", "data", "codata", "infixl", "infixr", "rec", "mu", "import", "Type", "CBV", "CBN"]

-- Check if the string is in the list of reserved keywords.
-- Reserved keywords cannot be used as identifiers.
checkReserved :: Text -> Parser ()
checkReserved str | str `elem` keywords = fail . T.unpack $ "Keyword " <> str <> " cannot be used as an identifier."
                  | otherwise = return ()

matchKwP :: Parser SourcePos
matchKwP = keywordP "match"

caseKwP :: Parser SourcePos
caseKwP = keywordP "case"

comatchKwP :: Parser SourcePos
comatchKwP = keywordP "comatch"

cocaseKwP :: Parser SourcePos
cocaseKwP = keywordP "cocase"

ofKwP :: Parser SourcePos
ofKwP = keywordP "of"

prdKwP :: Parser SourcePos
prdKwP = keywordP "prd"

cnsKwP :: Parser SourcePos
cnsKwP = keywordP "cns"

cmdKwP :: Parser SourcePos
cmdKwP = keywordP "cmd"

doneKwP :: Parser SourcePos
doneKwP = keywordP "Done"

printKwP :: Parser SourcePos
printKwP = keywordP "Print"

readKwP :: Parser SourcePos
readKwP = keywordP "Read"

forallKwP :: Parser SourcePos
forallKwP = keywordP "forall"

dataKwP :: Parser SourcePos
dataKwP = keywordP "data"

infixlKwP :: Parser SourcePos
infixlKwP = keywordP "infixl"

infixrKwP :: Parser SourcePos
infixrKwP = keywordP "infixr"

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

cbvKwP :: Parser SourcePos
cbvKwP = keywordP "CBV"

cbnKwP :: Parser SourcePos
cbnKwP = keywordP "CBN"

typeKwP :: Parser SourcePos
typeKwP = keywordP "Type"

-------------------------------------------------------------------------------------------
-- Symbols
-------------------------------------------------------------------------------------------

varianceP :: Parser Variance
varianceP = (string "+" >> pure Covariant) <|> (string "-" >> pure Contravariant)
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

thinRightarrow :: Parser SourcePos
thinRightarrow = symbol "->"

commandSym :: Parser SourcePos
commandSym = symbol ">>"

unionSym :: Parser SourcePos
unionSym = symbol "\\/"

intersectionSym :: Parser SourcePos
intersectionSym = symbol "/\\"

subtypeSym :: Parser SourcePos
subtypeSym = symbol "<:"

refineSym :: Parser SourcePos
refineSym = symbol ":>>"

implicitSym :: Parser SourcePos
implicitSym = symbol "*"

parSym :: Parser SourcePos
parSym = symbol "⅋"

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

-- | Parse a non-empty list of elements in parens.
-- E.g. "(a,a,a)"
parensListP :: Parser a -> Parser ([(PrdCns, a)], SourcePos)
parensListP p = parens  $ ((,) Prd <$> p) `sepBy` comma

-- | Parse a non-empty list of elements in parens, with exactly one asterisk.
-- E.g. "(a,*,a)"
parensListIP :: Parser a -> Parser (([(PrdCns, a)],[(PrdCns, a)]), SourcePos)
parensListIP p = parens $ do
  let p' =(\x -> (Prd, x)) <$> p
  fsts <- option [] (try ((p' `sepBy` try (comma <* notFollowedBy implicitSym)) <* comma))
  _ <- implicitSym
  snds <- option [] (try (comma *> p' `sepBy` comma))
  return (fsts, snds)

-- | Parse a non-empty list of elements in brackets.
-- E.g. "[a,a,a]"
bracketsListP :: Parser a -> Parser ([(PrdCns,a)], SourcePos)
bracketsListP p = brackets $ ((,) Cns <$> p) `sepBy` comma

-- | Parse a non-empty list of elements in parens, with exactly one asterisk.
-- E.g. "[a,*,a]"
bracketsListIP :: Parser a -> Parser (([(PrdCns, a)], [(PrdCns, a)]), SourcePos)
bracketsListIP p = brackets $ do
  let p' =(\x -> (Cns, x)) <$> p
  fsts <- option [] (try ((p' `sepBy` try (comma <* notFollowedBy implicitSym)) <* comma))
  _ <- implicitSym
  snds <- option [] (try (comma *> p' `sepBy` comma))
  return (fsts, snds)

-- | Parse a sequence of produer/consumer argument lists
argListsP ::  Parser a -> Parser ([(PrdCns,a)], SourcePos)
argListsP p = do
  endPos <- getSourcePos
  xs <- many (try (parensListP p) <|> try (bracketsListP p))
  case xs of
    [] -> return ([], endPos)
    xs -> return (concat (fst <$> xs), snd (last xs))

argListsIP :: PrdCns -> Parser a -> Parser (([(PrdCns,a)],(),[(PrdCns,a)]), SourcePos)
argListsIP mode p = do
  (fsts,_) <- argListsP p
  ((middle1, middle2),_) <- (if mode == Prd then parensListIP else bracketsListIP) p
  (lasts,endPos) <- argListsP p
  return ((fsts ++ middle1,(), middle2 ++ lasts), endPos)

-------------------------------------------------------------------------------------------
-- Recovery parser
-------------------------------------------------------------------------------------------

parseUntilKeywP :: Parser ()
parseUntilKeywP = do
  let endP = prdKwP <|> cnsKwP <|> cmdKwP <|> dataKwP <|> codataKwP <|>
             infixlKwP <|> infixrKwP <|> setKwP <|> (eof >> getSourcePos)
  _ <- manyTill anySingle (lookAhead endP)
  return ()

