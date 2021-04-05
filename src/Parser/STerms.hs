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
  v <- freeVarName
  return (FreeVar pc v)

numLitP :: PrdCnsRep pc -> Parser (STerm pc bs)
numLitP CnsRep = empty
numLitP PrdRep = numToTerm <$> numP
  where
    numToTerm :: Int -> STerm Prd bs
    numToTerm 0 = XtorCall PrdRep (MkXtorName Structural "Z") (MkXtorArgs [] [])
    numToTerm n = XtorCall PrdRep (MkXtorName Structural "S") (MkXtorArgs [numToTerm (n-1)] [])

lambdaSugar :: PrdCnsRep pc -> Parser (STerm pc FreeVarName)
lambdaSugar CnsRep = empty
lambdaSugar PrdRep= do
  _ <- symbol "\\"
  args <- argListP freeVarName freeVarName
  _ <- symbol "=>"
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
  xt <- xtorName ns
  args <- xtorArgsP
  return $ XtorCall pc xt args

patternMatch :: PrdCnsRep pc -> Parser (STerm pc FreeVarName)
patternMatch PrdRep = do
  _ <- symbol "comatch"
  (cases,ns) <- casesP
  return $ XMatch PrdRep ns cases
patternMatch CnsRep = do
  _ <- symbol "match"
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
  xt <- xtorName ns
  args <- argListP freeVarName freeVarName
  _ <- symbol "=>"
  cmd <- commandP
  return MkSCase { scase_name = xt
                 , scase_args = args
                 , scase_cmd = commandClosing args cmd -- de brujin transformation
                 }

muAbstraction :: PrdCnsRep pc -> Parser (STerm pc FreeVarName)
muAbstraction pc = do
  _ <- symbol (case pc of { PrdRep -> "mu"; CnsRep -> "mu*" })
  v <- freeVarName
  _ <- dot
  cmd <- commandP
  case pc of
    PrdRep -> return $ MuAbs pc v (commandClosingSingle CnsRep v cmd)
    CnsRep -> return $ MuAbs pc v (commandClosingSingle PrdRep v cmd)

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
  _ <- symbol ">>"
  cns <- stermP CnsRep
  return (Apply prd cns)

doneCmdP :: Parser (Command FreeVarName)
doneCmdP = do
  _ <- symbol "Done"
  return Done

printCmdP :: Parser (Command FreeVarName)
printCmdP = do
  _ <- symbol "Print"
  arg <- parens (stermP PrdRep)
  return $ Print arg

commandP :: Parser (Command FreeVarName)
commandP =
  try (parens commandP) <|>
  doneCmdP <|>
  printCmdP <|>
  applyCmdP

