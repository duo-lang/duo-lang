module Parser.Lexer
  ( sc
    -- Literals
  , natP
  , intP
  , uintP
  , floatP
    -- Names
  , freeVarName
  , tvarP
  , xtorName
  , typeNameP
  , moduleNameP
  , optionP
    -- Keywords
  , caseKwP
  , cocaseKwP
  , ofKwP
  , defKwP
  , doneKwP
  , printKwP
  , readKwP
  , forallKwP
  , dataKwP
  , codataKwP
  , recKwP
  , muKwP
  , importKwP
  , setKwP
  , topKwP
  , botKwP
  , i64KwP
  , f64KwP
  , cbvKwP
  , cbnKwP
  , i64RepKwP
  , f64RepKwP
  , typeKwP
  , refinementKwP
  , constructorKwP
  , destructorKwP
    -- Symbols
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
  , implicitSym
  , parSym
  , plusSym
  , minusSym
  , primitiveSym
  , primOpKeywordP
    -- Parens
  , angles
  , parens
  , brackets
  , braces
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
import Text.Megaparsec.Char.Lexer (decimal, signed, float)
import Syntax.Primitives (PrimitiveOp, primOpKeyword, PrimitiveType, primTypeKeyword)

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
sc = L.space space1 (L.skipLineComment "--") empty

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

natP :: Parser (Int, SourcePos)
natP = do
  (numStr, pos) <- lexeme (some numberChar)
  return (read numStr, pos)

uintP :: Parser (Integer, SourcePos)
uintP = do
  pos <- getSourcePos
  i <- decimal
  pure (i, pos)

intP :: Parser (Integer, SourcePos)
intP = do
  pos <- getSourcePos
  i <- signed space decimal
  pure (i, pos)

floatP :: Parser (Double, SourcePos)
floatP = do
  pos <- getSourcePos
  f <- signed space float
  pure (f, pos)

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
  return (MkFreeVarName name, pos)

tvarP :: Parser (TVar, SourcePos)
tvarP = try $ do
  (name, pos) <- lexeme $ (T.cons <$> lowerChar <*> (T.pack <$> many alphaNumChar))
  checkReserved name
  return (MkTVar name, pos)


checkTick :: NominalStructural -> Parser ()
checkTick Nominal = return ()
checkTick Refinement = return ()
checkTick Structural = () <$ tick

xtorName :: Parser (XtorName, SourcePos)
xtorName = try $ do
  (name, pos) <- lexeme $ T.cons <$> upperChar <*> (T.pack <$> many alphaNumChar)
  checkReserved name
  return (MkXtorName name, pos)

typeNameP :: Parser (TypeName, SourcePos)
typeNameP = try $ do
  (name, pos) <- lexeme $ T.cons <$> upperChar <*> (T.pack <$> many alphaNumChar)
  checkReserved name
  return (MkTypeName name, pos)

moduleNameP :: Parser (ModuleName, SourcePos)
moduleNameP = try $ do
  (name, pos) <- lexeme $ T.cons <$> upperChar <*> (T.pack <$> many alphaNumChar)
  checkReserved name
  return (MkModuleName name, pos)

-------------------------------------------------------------------------------------------
-- Keywords
-------------------------------------------------------------------------------------------

keywords :: [Text]
keywords = ["case", "cocase", "def", "of", "set", "Top", "Bot"
           , "Done", "Print", "Read", "forall", "data", "codata", "rec", "mu", "import", "Type"
           , "CBV", "CBN", "F64Rep", "I64Rep", "refinement", "constructor", "destructor"]

-- Check if the string is in the list of reserved keywords.
-- Reserved keywords cannot be used as identifiers.
checkReserved :: Text -> Parser ()
checkReserved str | str `elem` keywords = fail . T.unpack $ "Keyword " <> str <> " cannot be used as an identifier."
                  | otherwise = return ()

caseKwP :: Parser SourcePos
caseKwP = keywordP "case"

cocaseKwP :: Parser SourcePos
cocaseKwP = keywordP "cocase"

ofKwP :: Parser SourcePos
ofKwP = keywordP "of"

defKwP :: Parser SourcePos
defKwP = keywordP "def"

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

primitiveTyP :: String -> Parser SourcePos
primitiveTyP s = keywordP (T.pack ("#" ++ s))

i64KwP :: Parser SourcePos
i64KwP = primitiveTyP "I64"

f64KwP :: Parser SourcePos
f64KwP = primitiveTyP "F64"

cbvKwP :: Parser SourcePos
cbvKwP = keywordP "CBV"

cbnKwP :: Parser SourcePos
cbnKwP = keywordP "CBN"

i64RepKwP :: Parser SourcePos
i64RepKwP = keywordP "I64Rep"

f64RepKwP :: Parser SourcePos
f64RepKwP = keywordP "F64Rep"

typeKwP :: Parser SourcePos
typeKwP = keywordP "Type"

refinementKwP :: Parser SourcePos
refinementKwP = keywordP "refinement"

constructorKwP :: Parser SourcePos
constructorKwP = keywordP "constructor"

destructorKwP :: Parser SourcePos
destructorKwP = keywordP "destructor"

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

implicitSym :: Parser SourcePos
implicitSym = symbol "*"

parSym :: Parser SourcePos
parSym = symbol "⅋"

plusSym :: Parser SourcePos
plusSym = symbol "+"

minusSym :: Parser SourcePos
minusSym = symbol "-"

primitiveSym :: Parser SourcePos
primitiveSym = symbol "#"

primOpKeywordP :: PrimitiveType -> PrimitiveOp -> Parser (PrimitiveType, PrimitiveOp, SourcePos)
primOpKeywordP pt op = do
  endPos <- keywordP (T.pack (primOpKeyword op ++ primTypeKeyword pt))
  pure (pt, op, endPos)

-------------------------------------------------------------------------------------------
-- Parens
-------------------------------------------------------------------------------------------

betweenP :: Parser SourcePos -> Parser SourcePos -> Parser a -> Parser (a, SourcePos)
betweenP open close middle = do
  _ <- open
  res <- middle
  endPos <- close
  pure (res, endPos)

parens, braces, brackets, angles :: Parser a -> Parser (a, SourcePos)
parens    = betweenP (symbol "(")  (symbol ")")
braces    = betweenP (symbol "{")  (symbol "}")
brackets  = betweenP (symbol "[")  (symbol "]")
angles    = betweenP (symbol "<")  (symbol ">")

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

-- | Parse a sequence of producer/consumer argument lists
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
  let endP = defKwP <|> dataKwP <|> codataKwP <|> setKwP <|> refinementKwP <|> constructorKwP <|> destructorKwP <|> (eof >> getSourcePos)
  _ <- manyTill anySingle (lookAhead endP)
  return ()

