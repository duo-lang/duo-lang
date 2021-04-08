module Parser.ATerms ( atermP ) where

import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.CommonTerm
import Syntax.ATerms

fvarP :: Parser (ATerm () FreeVarName)
fvarP = do
  (fv, _pos) <- freeVarName
  return (FVar () fv)

ctorP :: NominalStructural -> Parser (ATerm () FreeVarName)
ctorP ns = do
  (xt, _pos) <- xtorName ns
  args <- option [] (parens $ atermP `sepBy` comma)
  return (Ctor () xt args)


dtorP :: NominalStructural -> Parser (ATerm () FreeVarName)
dtorP ns = do
  -- Must use atermP' here in order to avoid left-recursion in grammar!
  destructee <- atermP'
  _ <- dot
  (xt, _pos) <- xtorName ns
  args <- option [] (parens $ atermP `sepBy` comma)
  return (Dtor () xt destructee args)



acaseP :: NominalStructural -> Parser (ACase () FreeVarName)
acaseP ns = do
  (xt, _pos) <- xtorName ns
  args <- option [] (parens $ (fst <$> freeVarName) `sepBy` comma)
  _ <- rightarrow
  res <- atermP
  return (MkACase () xt args (atermClosing args res))

acasesP :: Parser [ACase () FreeVarName]
acasesP = try structuralCases <|> nominalCases
  where
    structuralCases = braces $ acaseP Structural `sepBy` comma
    nominalCases = braces $ acaseP Nominal `sepBy` comma

matchP :: Parser (ATerm () FreeVarName)
matchP = do
  _ <- matchKwP
  arg <- atermP
  _ <- withKwP
  cases <- acasesP
  return (Match () arg cases)

comatchP :: Parser (ATerm () FreeVarName)
comatchP = do
  _ <- comatchKwP
  cocases <- acasesP
  return (Comatch () cocases)

numLitP :: Parser (ATerm () bs)
numLitP = numToTerm . fst <$> numP
  where
    numToTerm :: Int -> ATerm () bs
    numToTerm 0 = Ctor () (MkXtorName Nominal "Z") []
    numToTerm n = Ctor () (MkXtorName Nominal "S") [numToTerm (n-1)]


-- | Like atermP but without dtorP, since dtorP
-- uses left-recursion in the grammar.
atermP' :: Parser (ATerm () FreeVarName)
atermP' =
  parens atermP <|>
  numLitP <|>
  matchP <|>
  comatchP <|>
  ctorP Structural <|>
  ctorP Nominal <|>
  fvarP

atermP :: Parser (ATerm () FreeVarName)
atermP =
  parens atermP <|>
  try (dtorP Structural) <|>
  try (dtorP Nominal) <|>
  numLitP <|>
  matchP <|>
  comatchP <|>
  ctorP Structural <|>
  ctorP Nominal <|>
  fvarP

