module Parser.ATerms ( atermP ) where

import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.CommonTerm
import Syntax.ATerms
import Utils (Loc(..))

fvarP :: Parser (ATerm Loc FreeVarName)
fvarP = do
  startPos <- getSourcePos
  (fv, endPos) <- freeVarName
  return (FVar (Loc startPos endPos) fv)

ctorP :: NominalStructural -> Parser (ATerm Loc FreeVarName)
ctorP ns = do
  startPos <- getSourcePos
  (xt, endPos) <- xtorName ns
  (args, endPos) <- option ([], endPos) (parens $ atermP `sepBy` comma)
  return (Ctor (Loc startPos endPos) xt args)


dtorP :: NominalStructural -> Parser (ATerm Loc FreeVarName)
dtorP ns = do
  startPos <- getSourcePos
  -- Must use atermP' here in order to avoid left-recursion in grammar!
  destructee <- atermP'
  _ <- dot
  (xt, endPos) <- xtorName ns
  (args, endPos) <- option ([], endPos) (parens $ atermP `sepBy` comma)
  return (Dtor (Loc startPos endPos) xt destructee args)



acaseP :: NominalStructural -> Parser (ACase Loc FreeVarName)
acaseP ns = do
  startPos <- getSourcePos
  (xt, _) <- xtorName ns
  args <- option [] (fst <$> (parens $ (fst <$> freeVarName) `sepBy` comma))
  _ <- rightarrow
  res <- atermP
  return (MkACase (Loc startPos undefined) xt args (atermClosing args res))

acasesP :: Parser ([ACase Loc FreeVarName], SourcePos)
acasesP = try structuralCases <|> nominalCases
  where
    structuralCases = braces $ acaseP Structural `sepBy` comma
    nominalCases = braces $ acaseP Nominal `sepBy` comma

matchP :: Parser (ATerm Loc FreeVarName)
matchP = do
  startPos <- getSourcePos
  _ <- matchKwP
  arg <- atermP
  _ <- withKwP
  (cases, endPos) <- acasesP
  return (Match (Loc startPos endPos) arg cases)

comatchP :: Parser (ATerm Loc FreeVarName)
comatchP = do
  startPos <- getSourcePos
  _ <- comatchKwP
  (cocases, endPos) <- acasesP
  return (Comatch (Loc startPos endPos) cocases)

numLitP :: Parser (ATerm Loc bs)
numLitP = do
  startPos <- getSourcePos
  (num, endPos) <- numP
  return (numToTerm  (Loc startPos endPos) num)
  where
    numToTerm :: Loc -> Int -> ATerm Loc bs
    numToTerm loc 0 = Ctor loc (MkXtorName Nominal "Z") []
    numToTerm loc n = Ctor loc (MkXtorName Nominal "S") [numToTerm loc (n-1)]


-- | Like atermP but without dtorP, since dtorP
-- uses left-recursion in the grammar.
atermP' :: Parser (ATerm Loc FreeVarName)
atermP' =
  (fst <$> (parens atermP)) <|>
  numLitP <|>
  matchP <|>
  comatchP <|>
  ctorP Structural <|>
  ctorP Nominal <|>
  fvarP

atermP :: Parser (ATerm Loc FreeVarName)
atermP =
  (fst <$> (parens atermP)) <|>
  try (dtorP Structural) <|>
  try (dtorP Nominal) <|>
  numLitP <|>
  matchP <|>
  comatchP <|>
  ctorP Structural <|>
  ctorP Nominal <|>
  fvarP

