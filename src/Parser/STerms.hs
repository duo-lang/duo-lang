module Parser.STerms
  ( stermP
  , commandP
  )where

import Text.Megaparsec hiding (State)


import Parser.Definition
import Parser.Lexer
import Syntax.STerms
import Utils

--------------------------------------------------------------------------------------------
-- Free Variables, Literals and Xtors
--------------------------------------------------------------------------------------------

freeVar :: PrdCnsRep pc -> Parser (STerm pc Loc bs, SourcePos)
freeVar pc = do
  startPos <- getSourcePos
  (v, endPos) <- freeVarName
  return (FreeVar (Loc startPos endPos) pc v, endPos)

numLitP :: NominalStructural -> PrdCnsRep pc -> Parser (STerm pc Loc bs, SourcePos)
numLitP _ CnsRep = empty
numLitP ns PrdRep = do
  startPos <- getSourcePos
  () <- checkTick ns
  (num, endPos) <- numP
  return (numToTerm (Loc startPos endPos) num, endPos)
  where
    numToTerm :: Loc -> Int -> STerm Prd Loc bs
    numToTerm loc 0 = XtorCall loc PrdRep (MkXtorName ns "Z") (MkXtorArgs [] [])
    numToTerm loc n = XtorCall loc PrdRep (MkXtorName ns "S") (MkXtorArgs [numToTerm loc (n-1)] [])

-- | Parse two lists, the first in parentheses and the second in brackets.
xtorArgsP :: Parser (XtorArgs Loc FreeVarName, SourcePos)
xtorArgsP = do
  endPos <- getSourcePos
  (xs, endPos) <- option ([],endPos) (parens   $ (fst <$> (stermP PrdRep)) `sepBy` comma)
  (ys, endPos) <- option ([],endPos) (brackets $ (fst <$> (stermP CnsRep)) `sepBy` comma)
  return (MkXtorArgs xs ys, endPos)

xtorCall :: NominalStructural -> PrdCnsRep pc -> Parser (STerm pc Loc FreeVarName, SourcePos)
xtorCall ns pc = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorName ns
  (args, endPos) <- xtorArgsP
  return (XtorCall (Loc startPos endPos) pc xt args, endPos)

--------------------------------------------------------------------------------------------
-- Pattern and copattern matches
--------------------------------------------------------------------------------------------

singleCase :: NominalStructural -> Parser (SCase Loc FreeVarName, SourcePos)
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
casesP :: Parser ([SCase Loc FreeVarName], NominalStructural,SourcePos)
casesP = try structuralCases <|> nominalCases
  where
    structuralCases = do
      (cases, endPos) <- braces ((fst <$> singleCase Structural) `sepBy` comma)
      return (cases, Structural, endPos)
    nominalCases = do
      (cases, endPos) <- braces ((fst <$> singleCase Nominal) `sepBy1` comma)
      -- There must be at least one case for a nominal type to be inferred
      return (cases, Nominal, endPos)

patternMatch :: PrdCnsRep pc -> Parser (STerm pc Loc FreeVarName, SourcePos)
patternMatch PrdRep = do
  startPos <- getSourcePos
  _ <- comatchKwP
  (cases,ns, endPos) <- casesP
  return (XMatch (Loc startPos endPos) PrdRep ns cases, endPos)
patternMatch CnsRep = do
  startPos <- getSourcePos
  _ <- matchKwP
  (cases,ns,endPos) <- casesP
  return (XMatch (Loc startPos endPos) CnsRep ns cases, endPos)

--------------------------------------------------------------------------------------------
-- Mu abstractions
--------------------------------------------------------------------------------------------

muAbstraction :: PrdCnsRep pc -> Parser (STerm pc Loc FreeVarName, SourcePos)
muAbstraction PrdRep = do
  startPos <- getSourcePos
  _ <- muKwP
  (v, _pos) <- freeVarName
  _ <- dot
  (cmd, endPos) <- commandP
  return (MuAbs (Loc startPos endPos) PrdRep v (commandClosingSingle CnsRep v cmd), endPos)
muAbstraction CnsRep = do
  startPos <- getSourcePos
  _ <- muKwP
  (v, _pos) <- freeVarName
  _ <- dot
  (cmd, endPos) <- commandP
  return (MuAbs (Loc startPos endPos) CnsRep v (commandClosingSingle PrdRep v cmd), endPos)

--------------------------------------------------------------------------------------------
-- Combined STerms parser
--------------------------------------------------------------------------------------------

stermP :: PrdCnsRep pc -> Parser (STerm pc Loc FreeVarName, SourcePos)
stermP pc = fst <$> (parens (stermP pc))
  <|> try (numLitP Structural pc)
  <|> try (numLitP Nominal pc)
  <|> xtorCall Structural pc
  <|> xtorCall Nominal pc
  <|> patternMatch pc
  <|> muAbstraction pc
  <|> freeVar pc

--------------------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------------------

applyCmdP :: Parser (Command Loc FreeVarName, SourcePos)
applyCmdP = do
  startPos <- getSourcePos
  (prd, _pos) <- stermP PrdRep
  _ <- commandSym
  (cns, endPos) <- stermP CnsRep
  return (Apply (Loc startPos endPos) Nothing prd cns, endPos)

doneCmdP :: Parser (Command Loc FreeVarName, SourcePos)
doneCmdP = do
  startPos <- getSourcePos
  endPos <- doneKwP
  return (Done (Loc startPos endPos), endPos)

printCmdP :: Parser (Command Loc FreeVarName, SourcePos)
printCmdP = do
  startPos <- getSourcePos
  _ <- printKwP
  (arg,endPos) <- parens (fst <$> stermP PrdRep)
  return (Print (Loc startPos endPos) arg, endPos)

commandP :: Parser (Command Loc FreeVarName, SourcePos)
commandP =
  try (fst <$> (parens commandP)) <|>
  doneCmdP <|>
  printCmdP <|>
  applyCmdP

