module Parser.ATerms ( atermP ) where

import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.CommonTerm
import Syntax.ATerms
import Utils (Loc(..))

-------------------------------------------------------------------------------------------
-- Free Variables
-------------------------------------------------------------------------------------------

fvarP :: Parser (ATerm Loc FreeVarName, SourcePos)
fvarP = do
  startPos <- getSourcePos
  (fv, endPos) <- freeVarName
  return (FVar (Loc startPos endPos) fv, endPos)

-------------------------------------------------------------------------------------------
-- Constructors, Destructors and Literals
-------------------------------------------------------------------------------------------

ctorP :: NominalStructural -> Parser (ATerm Loc FreeVarName, SourcePos)
ctorP ns = do
  startPos <- getSourcePos
  (xt, endPos) <- xtorName ns
  (args, endPos) <- option ([], endPos) (parens $ (fst <$> atermP) `sepBy` comma)
  return (Ctor (Loc startPos endPos) xt args, endPos)


dtorP :: NominalStructural -> Parser (ATerm Loc FreeVarName, SourcePos)
dtorP ns = do
  startPos <- getSourcePos
  -- Must use atermP' here in order to avoid left-recursion in grammar!
  (destructee, _pos) <- atermP'
  _ <- dot
  (xt, endPos) <- xtorName ns
  (args, endPos) <- option ([], endPos) (parens $ (fst <$> atermP) `sepBy` comma)
  return (Dtor (Loc startPos endPos) xt destructee args, endPos)

numLitP :: Parser (ATerm Loc bs, SourcePos)
numLitP = do
  startPos <- getSourcePos
  (num, endPos) <- numP
  return (numToTerm  (Loc startPos endPos) num, endPos)
  where
    numToTerm :: Loc -> Int -> ATerm Loc bs
    numToTerm loc 0 = Ctor loc (MkXtorName Nominal "Z") []
    numToTerm loc n = Ctor loc (MkXtorName Nominal "S") [numToTerm loc (n-1)]

-------------------------------------------------------------------------------------------
-- Pattern and Copattern Matches
-------------------------------------------------------------------------------------------

acaseP :: NominalStructural -> Parser (ACase Loc FreeVarName)
acaseP ns = do
  startPos <- getSourcePos
  (xt, _) <- xtorName ns
  args <- option [] (fst <$> (parens $ (fst <$> freeVarName) `sepBy` comma))
  _ <- rightarrow
  (res, endPos) <- atermP
  return (MkACase (Loc startPos endPos) xt args (atermClosing args res))

acasesP :: Parser ([ACase Loc FreeVarName], SourcePos)
acasesP = try structuralCases <|> nominalCases
  where
    structuralCases = braces $ acaseP Structural `sepBy` comma
    nominalCases = braces $ acaseP Nominal `sepBy` comma

matchP :: Parser (ATerm Loc FreeVarName, SourcePos)
matchP = do
  startPos <- getSourcePos
  _ <- matchKwP
  (arg, _pos) <- atermP
  _ <- withKwP
  (cases, endPos) <- acasesP
  return (Match (Loc startPos endPos) arg cases, endPos)

comatchP :: Parser (ATerm Loc FreeVarName, SourcePos)
comatchP = do
  startPos <- getSourcePos
  _ <- comatchKwP
  (cocases, endPos) <- acasesP
  return (Comatch (Loc startPos endPos) cocases, endPos)

-------------------------------------------------------------------------------------------
-- ATerm Parsers
-------------------------------------------------------------------------------------------

-- | Like atermP but without dtorP, since dtorP
-- uses left-recursion in the grammar.
atermP' :: Parser (ATerm Loc FreeVarName, SourcePos)
atermP' =
  parens (fst <$> atermP) <|>
  numLitP <|>
  matchP <|>
  comatchP <|>
  ctorP Structural <|>
  ctorP Nominal <|>
  fvarP

atermP :: Parser (ATerm Loc FreeVarName, SourcePos)
atermP =
  parens (fst <$> atermP) <|>
  try (dtorP Structural) <|>
  try (dtorP Nominal) <|>
  numLitP <|>
  matchP <|>
  comatchP <|>
  ctorP Structural <|>
  ctorP Nominal <|>
  fvarP

