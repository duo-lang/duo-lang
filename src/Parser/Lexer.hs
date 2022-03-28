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
  , tyOpNameP
  , moduleNameP
  -- Keywords
  , Keyword(..)
  , keywordP
  -- Symbols
  , Symbol(..)
  , symbolP
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
  , primOpKeywordP
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

operatorP :: Parser (Text, SourcePos)
operatorP = f <|> g
  where
    -- We have to treat the function arrow specially, since we want to allow it
    -- as an operator, but it is also a reserved symbol.
    f = symbolP SymSimpleRightArrow >>= \pos -> pure ("->",pos)
    g = do
      (name, pos) <- lexeme $ T.pack <$> many (symbolChar <|> punctuationChar)
      checkReservedOp name
      pure (name, pos)

---

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

tyOpNameP :: Parser (TyOpName, SourcePos)
tyOpNameP = try $ do
  (name, pos) <- operatorP
  return (MkTyOpName name, pos)

checkTick :: NominalStructural -> Parser ()
checkTick Nominal = return ()
checkTick Refinement = return ()
checkTick Structural = () <$ symbolP SymTick

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
  KwOperator    :: Keyword
  KwAt          :: Keyword
  KwLeftAssoc   :: Keyword
  KwRightAssoc  :: Keyword
  -- Command Keywords
  KwDone        :: Keyword
  KwPrint       :: Keyword
  KwRead        :: Keyword
  -- Declaration Keywords
  KwType        :: Keyword
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
  show KwOperator    = "operator"
  show KwAt          = "at"
  show KwLeftAssoc   = "leftassoc"
  show KwRightAssoc  = "rightassoc"
  -- Command Keywords
  show KwDone        = "Done"
  show KwPrint       = "Print"
  show KwRead        = "Read"
  -- Declaration Keywords
  show KwType        = "type"
  show KwRefinement  = "refinement"
  show KwConstructor = "constructor"
  show KwDestructor  = "destructor"
  show KwDef         = "def"
  show KwData        = "data"
  show KwCodata      = "codata"
  show KwSet         = "set"
  show KwImport      = "import"
  

-- | These keywords start a new declaration at the toplevel and
--   are used to restart parsing after a parse error has been
--   encountered.
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
isDeclarationKw KwOperator    = False
isDeclarationKw KwAt          = False
isDeclarationKw KwLeftAssoc   = False
isDeclarationKw KwRightAssoc  = False
-- Command Keywords
isDeclarationKw KwDone        = False
isDeclarationKw KwPrint       = False
isDeclarationKw KwRead        = False
-- Declaration Keywords
isDeclarationKw KwType        = True
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

-- | All keywords which start toplevel declarations
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

data Symbol where
  SymComma            :: Symbol
  SymDot              :: Symbol
  SymSemi             :: Symbol
  SymColon            :: Symbol
  SymPipe             :: Symbol
  SymTick             :: Symbol
  SymBackslash        :: Symbol
  SymColoneq          :: Symbol
  SymDoubleRightArrow :: Symbol
  SymSimpleRightArrow :: Symbol
  SymCommand          :: Symbol
  SymUnion            :: Symbol
  SymIntersection     :: Symbol
  SymSubtype          :: Symbol
  SymImplicit         :: Symbol
  SymPlus             :: Symbol
  SymMinus            :: Symbol
  SymHash             :: Symbol
  -- Parens Symbols
  SymParenLeft        :: Symbol
  SymParenRight       :: Symbol
  SymBraceLeft        :: Symbol
  SymBraceRight       :: Symbol
  SymBracketLeft      :: Symbol
  SymBracketRight     :: Symbol
  SymAngleLeft        :: Symbol
  SymAngleRight       :: Symbol
  deriving (Eq, Ord, Enum, Bounded)

instance Show Symbol where
  show SymComma            = ","
  show SymDot              = "."
  show SymSemi             = ";"
  show SymColon            = ":"
  show SymPipe             = "|"
  show SymTick             = "'"
  show SymBackslash        = "\\"
  show SymColoneq          = ":="
  show SymDoubleRightArrow = "=>"
  show SymSimpleRightArrow = "->"
  show SymCommand          = ">>"
  show SymUnion            = "\\/"
  show SymIntersection     = "/\\"
  show SymSubtype          = "<:"
  show SymImplicit         = "*"
  show SymPlus             = "+"
  show SymMinus            = "-"
  show SymHash             = "#"
  -- Parens Symbols
  show SymParenLeft        = "("
  show SymParenRight       = ")"
  show SymBraceLeft        = "{"
  show SymBraceRight       = "}"
  show SymBracketLeft      = "["
  show SymBracketRight     = "]"
  show SymAngleLeft        = "<"
  show SymAngleRight       = ">"

symbolP :: Symbol -> Parser SourcePos
symbolP sym = do
  _ <- string (T.pack (show sym))
  endPos <- getSourcePos
  sc
  return endPos

operators :: [Symbol]
operators = enumFromTo minBound maxBound

-- Check if the string is in the list of reserved operators.
-- Reserved operators cannot be used as custom operators
checkReservedOp :: Text -> Parser ()
checkReservedOp str | any ((flip T.isInfixOf) str) (T.pack . show <$> operators) = fail . T.unpack $ "Operator " <> str <> " cannot be used as a custom operator."
                    | otherwise = return ()

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
parens    = betweenP (symbolP SymParenLeft)   (symbolP SymParenRight)
braces    = betweenP (symbolP SymBraceLeft)   (symbolP SymBraceRight)
brackets  = betweenP (symbolP SymBracketLeft) (symbolP SymBracketRight)
angles    = betweenP (symbolP SymAngleLeft)   (symbolP SymAngleRight)

-- | Parse a non-empty list of elements in parens.
-- E.g. "(a,a,a)"
parensListP :: Parser a -> Parser ([(PrdCns, a)], SourcePos)
parensListP p = parens  $ ((,) Prd <$> p) `sepBy` symbolP SymComma

-- | Parse a non-empty list of elements in parens, with exactly one asterisk.
-- E.g. "(a,*,a)"
parensListIP :: Parser a -> Parser (([(PrdCns, a)],[(PrdCns, a)]), SourcePos)
parensListIP p = parens $ do
  let p' =(\x -> (Prd, x)) <$> p
  fsts <- option [] (try ((p' `sepBy` try (symbolP SymComma <* notFollowedBy (symbolP SymImplicit))) <* symbolP SymComma))
  _ <- symbolP SymImplicit
  snds <- option [] (try (symbolP SymComma *> p' `sepBy` symbolP SymComma))
  return (fsts, snds)

-- | Parse a non-empty list of elements in brackets.
-- E.g. "[a,a,a]"
bracketsListP :: Parser a -> Parser ([(PrdCns,a)], SourcePos)
bracketsListP p = brackets $ ((,) Cns <$> p) `sepBy` symbolP SymComma

-- | Parse a non-empty list of elements in parens, with exactly one asterisk.
-- E.g. "[a,*,a]"
bracketsListIP :: Parser a -> Parser (([(PrdCns, a)], [(PrdCns, a)]), SourcePos)
bracketsListIP p = brackets $ do
  let p' =(\x -> (Cns, x)) <$> p
  fsts <- option [] (try ((p' `sepBy` try (symbolP SymComma <* notFollowedBy (symbolP SymImplicit))) <* symbolP SymComma))
  _ <- symbolP SymImplicit
  snds <- option [] (try (symbolP SymComma *> p' `sepBy` symbolP SymComma))
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



