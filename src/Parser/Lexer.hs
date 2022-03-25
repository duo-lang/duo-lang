module Parser.Lexer
  ( sc
    -- Literals
  , natP
  , intP
  , uintP
  , floatP
    -- Names
  , allCaseId
  , freeVarName
  , tvarP
  , xtorName
  , typeNameP
  , moduleNameP
  -- Keywords
  , Keyword(..)
  , keywordP
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

import Data.Foldable (asum)
import Data.Text (Text)
import Data.Text qualified as T
import Text.Megaparsec hiding (State)
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer qualified as L

import Parser.Definition
import Syntax.Common
import Text.Megaparsec.Char.Lexer (decimal, signed, float)

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

-------------------------------------------------------------------------------------------
-- Names
-------------------------------------------------------------------------------------------

lowerCaseId :: Parser (Text, SourcePos)
lowerCaseId = do
  (name, pos) <- lexeme $ (T.cons <$> lowerChar <*> (T.pack <$> many alphaNumChar))
  checkReserved name
  pure (name, pos)

upperCaseId :: Parser (Text, SourcePos)
upperCaseId = do
  (name, pos) <- lexeme $ T.cons <$> upperChar <*> (T.pack <$> many alphaNumChar)
  checkReserved name
  pure (name, pos)

allCaseId :: Parser (Text, SourcePos)
allCaseId = do
  (name, pos) <- lexeme $ T.pack <$> many alphaNumChar
  checkReserved name
  pure (name, pos)

freeVarName :: Parser (FreeVarName, SourcePos)
freeVarName = try $ do
  (name, pos) <- lowerCaseId
  return (MkFreeVarName name, pos)

tvarP :: Parser (TVar, SourcePos)
tvarP = try $ do
  (name, pos) <- lowerCaseId
  return (MkTVar name, pos)

xtorName :: Parser (XtorName, SourcePos)
xtorName = try $ do
  (name, pos) <- upperCaseId
  return (MkXtorName name, pos)

typeNameP :: Parser (TypeName, SourcePos)
typeNameP = try $ do
  (name, pos) <- upperCaseId
  return (MkTypeName name, pos)

moduleNameP :: Parser (ModuleName, SourcePos)
moduleNameP = try $ do
  (name, pos) <- upperCaseId
  return (MkModuleName name, pos)

checkTick :: NominalStructural -> Parser ()
checkTick Nominal = return ()
checkTick Refinement = return ()
checkTick Structural = () <$ tick

-------------------------------------------------------------------------------------------
-- Keywords
-------------------------------------------------------------------------------------------

data Keyword where
  -- Term Keywords
  KwCase        :: Keyword
  KwCocase      :: Keyword
  KwOf          :: Keyword
  KwMu          :: Keyword
  -- Type and Kind Keywords
  KwForall      :: Keyword
  KwRec         :: Keyword
  KwTop         :: Keyword
  KwBot         :: Keyword
  KwCBV         :: Keyword
  KwCBN         :: Keyword
  KwI64         :: Keyword
  KwF64         :: Keyword
  KwF64Rep      :: Keyword
  KwI64Rep      :: Keyword
  -- Command Keywords
  KwDone        :: Keyword
  KwPrint       :: Keyword
  KwRead        :: Keyword
  -- Declaration Keywords
  KwRefinement  :: Keyword
  KwConstructor :: Keyword
  KwDestructor  :: Keyword
  KwDef         :: Keyword
  KwData        :: Keyword
  KwCodata      :: Keyword
  KwSet         :: Keyword
  KwImport      :: Keyword
  deriving (Eq, Ord, Enum, Bounded)

instance Show Keyword where
  -- Term Keywords
  show KwCase        = "case"
  show KwCocase      = "cocase"
  show KwOf          = "of"
  show KwMu          = "mu"
  -- Type and Kind Keywords
  show KwForall      = "forall"
  show KwRec         = "rec"
  show KwTop         = "Top"
  show KwBot         = "Bot"
  show KwCBV         = "CBV"
  show KwCBN         = "CBN"
  show KwI64         = "#I64"
  show KwF64         = "#F64"
  show KwF64Rep      = "F64Rep"
  show KwI64Rep      = "I64Rep"
  -- Command Keywords
  show KwDone        = "Done"
  show KwPrint       = "Print"
  show KwRead        = "Read"
  -- Declaration Keywords
  show KwRefinement  = "refinement"
  show KwConstructor = "constructor"
  show KwDestructor  = "destructor"
  show KwDef         = "def"
  show KwData        = "data"
  show KwCodata      = "codata"
  show KwSet         = "set"
  show KwImport      = "import"
  

-- | Which keywords start a toplevel declaration.
-- These keywords are used to restart parsing after a parse error.
isDeclarationKw :: Keyword -> Bool
-- Term Keywords
isDeclarationKw KwCase        = False
isDeclarationKw KwCocase      = False
isDeclarationKw KwOf          = False
isDeclarationKw KwMu          = False
-- Type and Kind Keywords
isDeclarationKw KwForall      = False
isDeclarationKw KwRec         = False
isDeclarationKw KwTop         = False
isDeclarationKw KwBot         = False
isDeclarationKw KwCBV         = False
isDeclarationKw KwCBN         = False
isDeclarationKw KwI64         = False
isDeclarationKw KwF64         = False
isDeclarationKw KwF64Rep      = False
isDeclarationKw KwI64Rep      = False
-- Command Keywords
isDeclarationKw KwDone        = False
isDeclarationKw KwPrint       = False
isDeclarationKw KwRead        = False
-- Declaration Keywords
isDeclarationKw KwRefinement  = True
isDeclarationKw KwConstructor = True
isDeclarationKw KwDestructor  = True
isDeclarationKw KwDef         = True
isDeclarationKw KwData        = True
isDeclarationKw KwCodata      = True
isDeclarationKw KwSet         = True
isDeclarationKw KwImport      = True

-- | All keywords of the language
keywords :: [Keyword]
keywords = enumFromTo minBound maxBound

-- | All keywords which start toplevel Declarations
declKeywords :: [Keyword]
declKeywords = filter isDeclarationKw keywords

-- | A parser which parses a keyword
keywordP :: Keyword -> Parser SourcePos
keywordP kw = do
  _ <- string (T.pack (show kw)) <* notFollowedBy alphaNumChar
  endPos <- getSourcePos
  sc
  return endPos

parseUntilKeywP :: Parser ()
parseUntilKeywP = do
  let endP = asum ([keywordP kw | kw <- declKeywords] ++ [eof >> getSourcePos])
  _ <- manyTill anySingle (lookAhead endP)
  return ()


-- Check if the string is in the list of reserved keywords.
-- Reserved keywords cannot be used as identifiers.
checkReserved :: Text -> Parser ()
checkReserved str | str `elem` (T.pack . show <$> keywords) = fail . T.unpack $ "Keyword " <> str <> " cannot be used as an identifier."
                  | otherwise = return ()

primOpKeywordP :: PrimitiveType -> PrimitiveOp -> Parser (PrimitiveType, PrimitiveOp, SourcePos)
primOpKeywordP pt op = do
  _ <- string (T.pack (primOpKeyword op ++ primTypeKeyword pt))
  endPos <- getSourcePos
  sc
  pure (pt, op, endPos)

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



