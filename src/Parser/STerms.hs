module Parser.STerms
  ( stermP
  , commandP
  )where

import Text.Megaparsec hiding (State)


import Parser.Definition
import Parser.Lexer
import Syntax.STerms

--------------------------------------------------------------------------------------------
-- Symmetric Terms
--------------------------------------------------------------------------------------------

freeVar :: PrdCnsRep pc -> Parser (STerm pc bs)
freeVar pc = do
  (v, _pos) <- freeVarName
  return (FreeVar pc v)

numLitP :: PrdCnsRep pc -> Parser (STerm pc bs)
numLitP CnsRep = empty
numLitP PrdRep = numToTerm . fst <$> numP
  where
    numToTerm :: Int -> STerm Prd bs
    numToTerm 0 = XtorCall PrdRep (MkXtorName Structural "Z") (MkXtorArgs [] [])
    numToTerm n = XtorCall PrdRep (MkXtorName Structural "S") (MkXtorArgs [numToTerm (n-1)] [])

lambdaSugar :: PrdCnsRep pc -> Parser (STerm pc FreeVarName)
lambdaSugar CnsRep = empty
lambdaSugar PrdRep= do
  _ <- backslash
  args <- argListP (fst <$> freeVarName) (fst <$> freeVarName)
  _ <- rightarrow
  cmd <- commandP
  return $ XMatch PrdRep Structural [MkSCase (MkXtorName Structural "Ap") args (commandClosing args cmd)]

-- | Parse two lists, the first in parentheses and the second in brackets.
xtorArgsP :: Parser (XtorArgs FreeVarName)
xtorArgsP = do
  xs <- option [] (parens   $ (stermP PrdRep) `sepBy` comma)
  ys <- option [] (brackets $ (stermP CnsRep) `sepBy` comma)
  return $ MkXtorArgs xs ys

xtorCall :: NominalStructural -> PrdCnsRep pc -> Parser (STerm pc FreeVarName)
xtorCall ns pc = do
  (xt, _pos) <- xtorName ns
  args <- xtorArgsP
  return $ XtorCall pc xt args

patternMatch :: PrdCnsRep pc -> Parser (STerm pc FreeVarName)
patternMatch PrdRep = do
  _ <- comatchKwP
  (cases,ns) <- casesP
  return $ XMatch PrdRep ns cases
patternMatch CnsRep = do
  _ <- matchKwP
  (cases,ns) <- casesP
  return $ XMatch CnsRep ns cases

-- We put the structural pattern match parser before the nominal one, since in the case of an empty match/comatch we want to
-- infer a structural type, not a nominal one.
casesP :: Parser ([SCase FreeVarName], NominalStructural)
casesP = try structuralCases <|> nominalCases
  where
    structuralCases = braces $ do
      cases <- singleCase Structural `sepBy` comma
      return (cases, Structural)
    nominalCases = braces $ do
      -- There must be at least one case for a nominal type to be inferred
      cases <- singleCase Nominal `sepBy1` comma
      return (cases, Nominal)

singleCase :: NominalStructural -> Parser (SCase FreeVarName)
singleCase ns = do
  (xt, _pos) <- xtorName ns
  args <- argListP (fst <$> freeVarName) (fst <$> freeVarName)
  _ <- rightarrow
  cmd <- commandP
  return MkSCase { scase_name = xt
                 , scase_args = args
                 , scase_cmd = commandClosing args cmd -- de brujin transformation
                 }

muAbstraction :: PrdCnsRep pc -> Parser (STerm pc FreeVarName)
muAbstraction PrdRep = do
  _ <- muKwP
  (v, _pos) <- freeVarName
  _ <- dot
  cmd <- commandP
  return $ MuAbs PrdRep v (commandClosingSingle CnsRep v cmd)
muAbstraction CnsRep = do
  _ <- muStarKwP
  (v, _pos) <- freeVarName
  _ <- dot
  cmd <- commandP
  return $ MuAbs CnsRep v (commandClosingSingle PrdRep v cmd)

stermP :: PrdCnsRep pc -> Parser (STerm pc FreeVarName)
stermP pc = parens (stermP pc)
  <|> xtorCall Structural pc
  <|> xtorCall Nominal pc
  <|> patternMatch pc
  <|> muAbstraction pc
  <|> freeVar pc
  <|> numLitP pc
  <|> lambdaSugar pc

--------------------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------------------

applyCmdP :: Parser (Command FreeVarName)
applyCmdP = do
  prd <- stermP PrdRep
  _ <- commandSym
  cns <- stermP CnsRep
  return (Apply prd cns)

doneCmdP :: Parser (Command FreeVarName)
doneCmdP = do
  _ <- doneKwP
  return Done

printCmdP :: Parser (Command FreeVarName)
printCmdP = do
  _ <- printKwP
  arg <- parens (stermP PrdRep)
  return $ Print arg

commandP :: Parser (Command FreeVarName)
commandP =
  try (parens commandP) <|>
  doneCmdP <|>
  printCmdP <|>
  applyCmdP

