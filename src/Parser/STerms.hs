module Parser.STerms
  ( stermP
  , commandP
  )where

import Text.Megaparsec hiding (State)


import Parser.Definition
import Parser.Lexer
import Syntax.STerms

--------------------------------------------------------------------------------------------
-- Free Variables, Literals and Xtors
--------------------------------------------------------------------------------------------

freeVar :: PrdCnsRep pc -> Parser (STerm pc () bs, SourcePos)
freeVar pc = do
  (v, endPos) <- freeVarName
  return (FreeVar () pc v, endPos)

numLitP :: PrdCnsRep pc -> Parser (STerm pc () bs, SourcePos)
numLitP CnsRep = empty
numLitP PrdRep = do
  (num, endPos) <- numP
  return (numToTerm num, endPos)
  where
    numToTerm :: Int -> STerm Prd () bs
    numToTerm 0 = XtorCall () PrdRep (MkXtorName Structural "Z") (MkXtorArgs [] [])
    numToTerm n = XtorCall () PrdRep (MkXtorName Structural "S") (MkXtorArgs [numToTerm (n-1)] [])

lambdaSugar :: PrdCnsRep pc -> Parser (STerm pc () FreeVarName, SourcePos)
lambdaSugar CnsRep = empty
lambdaSugar PrdRep= do
  _ <- backslash
  (args, _) <- argListP (fst <$> freeVarName) (fst <$> freeVarName)
  _ <- rightarrow
  (cmd, endPos) <- commandP
  return (XMatch () PrdRep Structural [MkSCase (MkXtorName Structural "Ap") args (commandClosing args cmd)], endPos)

-- | Parse two lists, the first in parentheses and the second in brackets.
xtorArgsP :: Parser (XtorArgs () FreeVarName, SourcePos)
xtorArgsP = do
  endPos <- getSourcePos
  (xs, endPos) <- option ([],endPos) (parens   $ (fst <$> (stermP PrdRep)) `sepBy` comma)
  (ys, endPos) <- option ([],endPos) (brackets $ (fst <$> (stermP CnsRep)) `sepBy` comma)
  return (MkXtorArgs xs ys, endPos)

xtorCall :: NominalStructural -> PrdCnsRep pc -> Parser (STerm pc () FreeVarName, SourcePos)
xtorCall ns pc = do
  (xt, _pos) <- xtorName ns
  (args, endPos) <- xtorArgsP
  return (XtorCall () pc xt args, endPos)

--------------------------------------------------------------------------------------------
-- Pattern and copattern matches
--------------------------------------------------------------------------------------------

singleCase :: NominalStructural -> Parser (SCase () FreeVarName, SourcePos)
singleCase ns = do
  (xt, _pos) <- xtorName ns
  (args,_) <- argListP (fst <$> freeVarName) (fst <$> freeVarName)
  _ <- rightarrow
  (cmd, endPos) <- commandP
  let pmcase = MkSCase { scase_name = xt
                       , scase_args = args
                       , scase_cmd = commandClosing args cmd -- de brujin transformation
                       }
  return (pmcase, endPos)


-- We put the structural pattern match parser before the nominal one, since in the case of an empty match/comatch we want to
-- infer a structural type, not a nominal one.
casesP :: Parser ([SCase () FreeVarName], NominalStructural,SourcePos)
casesP = try structuralCases <|> nominalCases
  where
    structuralCases = do
      (cases, endPos) <- braces ((fst <$> singleCase Structural) `sepBy` comma)
      return (cases, Structural, endPos)
    nominalCases = do
      (cases, endPos) <- braces ((fst <$> singleCase Nominal) `sepBy1` comma)
      -- There must be at least one case for a nominal type to be inferred
      return (cases, Nominal, endPos)

patternMatch :: PrdCnsRep pc -> Parser (STerm pc () FreeVarName, SourcePos)
patternMatch PrdRep = do
  _ <- comatchKwP
  (cases,ns, endPos) <- casesP
  return (XMatch () PrdRep ns cases, endPos)
patternMatch CnsRep = do
  _ <- matchKwP
  (cases,ns,endPos) <- casesP
  return (XMatch () CnsRep ns cases, endPos)

--------------------------------------------------------------------------------------------
-- Mu abstractions
--------------------------------------------------------------------------------------------

muAbstraction :: PrdCnsRep pc -> Parser (STerm pc () FreeVarName, SourcePos)
muAbstraction PrdRep = do
  _ <- muKwP
  (v, _pos) <- freeVarName
  _ <- dot
  (cmd, endPos) <- commandP
  return (MuAbs () PrdRep v (commandClosingSingle CnsRep v cmd), endPos)
muAbstraction CnsRep = do
  _ <- muStarKwP
  (v, _pos) <- freeVarName
  _ <- dot
  (cmd, endPos) <- commandP
  return (MuAbs () CnsRep v (commandClosingSingle PrdRep v cmd), endPos)

--------------------------------------------------------------------------------------------
-- Combined STerms parser
--------------------------------------------------------------------------------------------

stermP :: PrdCnsRep pc -> Parser (STerm pc () FreeVarName, SourcePos)
stermP pc = fst <$> (parens (stermP pc))
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

applyCmdP :: Parser (Command () FreeVarName, SourcePos)
applyCmdP = do
  (prd, _pos) <- stermP PrdRep
  _ <- commandSym
  (cns, endPos) <- stermP CnsRep
  return (Apply () prd cns, endPos)

doneCmdP :: Parser (Command () FreeVarName, SourcePos)
doneCmdP = do
  endPos <- doneKwP
  return (Done (), endPos)

printCmdP :: Parser (Command () FreeVarName, SourcePos)
printCmdP = do
  _ <- printKwP
  (arg,endPos) <- parens (fst <$> stermP PrdRep)
  return (Print () arg, endPos)

commandP :: Parser (Command () FreeVarName, SourcePos)
commandP =
  try (fst <$> (parens commandP)) <|>
  doneCmdP <|>
  printCmdP <|>
  applyCmdP

