module Parser.Terms
  ( termP
  , commandP
  )where

import Data.Bifunctor (first)
import Data.List.NonEmpty (NonEmpty(..))
import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.CST.Terms qualified as CST
import Syntax.Common
import Utils

--------------------------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------------------------

xtorNameP :: Parser (XtorName, SourcePos)
xtorNameP = xtorName Nominal <|> xtorName Structural

--------------------------------------------------------------------------------------------
-- Substitutions and implicit substitutions
--------------------------------------------------------------------------------------------

mkTerm :: (PrdCns, CST.Term) -> CST.PrdCnsTerm
mkTerm (Prd, tm) = CST.PrdTerm tm
mkTerm (Cns, tm) = CST.CnsTerm tm

-- | Parse a substitution, consisting of lists of producers and consumers.
-- E.g.: "[cns,cns](prd)[cns](prd,prd)"
substitutionP :: Parser (CST.Substitution, SourcePos)
substitutionP = first (fmap mkTerm) <$> argListsP (fst <$> termTopP)

substitutionIP :: Parser (CST.SubstitutionI, SourcePos)
substitutionIP = do
  ((subst1,(),subst2), endPos) <- argListsIP Cns (fst <$> termTopP)
  return ((mkTerm <$> subst1, Prd, mkTerm <$> subst2), endPos)

--------------------------------------------------------------------------------------------
-- Binding sites and implicit binding sites
--------------------------------------------------------------------------------------------

bindingSiteP :: Parser (CST.BindingSite, SourcePos)
bindingSiteP = argListsP (fst <$> freeVarName)

bindingSiteIP :: Parser (CST.BindingSiteI, SourcePos)
bindingSiteIP = argListsIP Cns (fst <$> freeVarName)

--------------------------------------------------------------------------------------------
-- Free Variables, Literals and Xtors
--------------------------------------------------------------------------------------------

freeVar :: Parser (CST.Term, SourcePos)
freeVar = do
  startPos <- getSourcePos
  (v, endPos) <- freeVarName
  return (CST.Var (Loc startPos endPos) v, endPos)

natLitP :: NominalStructural -> Parser (CST.Term, SourcePos)
natLitP ns = do
  startPos <- getSourcePos
  () <- checkTick ns
  (num, endPos) <- numP
  return (CST.NatLit (Loc startPos endPos) ns num, endPos)

xtorP :: Parser (CST.Term, SourcePos)
xtorP = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorNameP
  (subst, endPos) <- substitutionP
  return (CST.Xtor (Loc startPos endPos) xt subst, endPos)

--------------------------------------------------------------------------------------------
-- Mu abstractions
--------------------------------------------------------------------------------------------

muAbstraction :: Parser (CST.Term, SourcePos)
muAbstraction = do
  startPos <- getSourcePos
  _ <- muKwP
  (v, _pos) <- freeVarName
  _ <- dot
  (cmd, endPos) <- cstcommandP
  return (CST.MuAbs (Loc startPos endPos) v cmd, endPos)

--------------------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------------------

applyCmdP :: Parser (CST.Command, SourcePos)
applyCmdP = do
  startPos <- getSourcePos
  (prd, _pos) <- try (termTopP <* commandSym)
  (cns, endPos) <- termTopP
  return (CST.Apply (Loc startPos endPos) prd cns, endPos)

doneCmdP :: Parser (CST.Command, SourcePos)
doneCmdP = do
  startPos <- getSourcePos
  endPos <- doneKwP
  return (CST.Done (Loc startPos endPos), endPos)

printCmdP :: Parser (CST.Command, SourcePos)
printCmdP = do
  startPos <- getSourcePos
  _ <- printKwP
  (arg,_) <- parens (fst <$> termTopP)
  _ <- semi
  (cmd, endPos) <- cstcommandP
  return (CST.Print (Loc startPos endPos) arg cmd, endPos)

readCmdP :: Parser (CST.Command, SourcePos)
readCmdP = do
  startPos <- getSourcePos
  _ <- readKwP
  (arg,endPos) <- brackets (fst <$> termTopP)
  return (CST.Read (Loc startPos endPos) arg, endPos)

commandVar :: Parser (CST.Command, SourcePos)
commandVar = do
  startPos <- getSourcePos
  (nm, endPos) <- freeVarName
  return (CST.Call (Loc startPos endPos) nm, endPos)

commandParensP :: Parser (CST.Command, SourcePos)
commandParensP = do
  startPos <- getSourcePos
  ((cmd,_), endPos) <- parens cstcommandP
  return (CST.CommandParens (Loc startPos endPos) cmd, endPos)

cstcommandP :: Parser (CST.Command, SourcePos)
cstcommandP =
  try commandParensP
  <|> doneCmdP
  <|> printCmdP
  <|> readCmdP
  <|> applyCmdP
  <|> commandVar

-------------------------------------------------------------------------------------------
-- BNF Grammar
-------------------------------------------------------------------------------------------

-- e  ::= e e                              Application                (Syntax Sugar)
--      | e.D(e,...,e)                     Dtor
--      | n                                Natural number literal     (Syntax Sugar)
--      | x                                Variable
--      | C(e,...,e)                       Ctor
--      | match { scase,...,scase }        Pattern match (symmetric)
--      | case e of { acase,...,acase }    Pattern match (asymmetric)
--      | comatch { scase,...,scase }      Copattern match (symmetric)
--      | cocase { acase,..., acase }      Copattern match (asymmetric)
--      | (e)                              Parenthesized expression
--      | \x => e                          Lambda abstraction         (Syntax sugar)
--
-- case   ::= X(x,...,x) => e

-- This ambiguous grammar can be disambiguated into the following set of grammars,
-- with abbreviations t(top), m(middle), b(bottom)

-- b  ::= x
--      | n
--      | C(t,...,t)
--      | match t with {...}
--      | comatch {...}
--      | (t)
--      | \x => t
--
-- m ::= b ... b (n-ary application, left associative, n >= 1)
--     | b
--
-- t ::= m.D(t,...,t). ... .D(t,...,t) (n-ary destructor application, n >= 1)
--     | m


-------------------------------------------------------------------------------------------
-- Bottom Parser
-------------------------------------------------------------------------------------------
--------------------------------------------------------------------------------------------
-- XMatches
--------------------------------------------------------------------------------------------

cmdcaseP :: Parser (CST.CommandCase, SourcePos)
cmdcaseP = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorNameP
  (args,_) <- bindingSiteP
  _ <- rightarrow
  (cmd, endPos) <- cstcommandP
  let pmcase = (Loc startPos endPos, xt, args, cmd)
  return (pmcase, endPos)

xmatchP :: Parser (CST.Term, SourcePos)
xmatchP = do
  startPos <- getSourcePos
  _ <- matchKwP <|> comatchKwP
  (cases, endPos) <- braces ((fst <$> cmdcaseP) `sepBy` comma)
  return (CST.XMatch (Loc startPos endPos) cases, endPos)

--------------------------------------------------------------------------------------------
-- Case-of
--------------------------------------------------------------------------------------------

termCaseP :: Parser (CST.TermCase, SourcePos)
termCaseP = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorNameP
  (args,_) <- bindingSiteP
  _ <- rightarrow
  (res, endPos) <- termTopP
  let pmcase = (Loc startPos endPos, xt, args, res)
  return (pmcase, endPos)

caseofP :: Parser (CST.Term, SourcePos)
caseofP = do
  startPos <- getSourcePos
  _ <- caseKwP
  (arg, _pos) <- termTopP
  _ <- ofKwP
  (cases, endPos) <- braces ((fst <$> termCaseP) `sepBy` comma)
  return (CST.Case (Loc startPos endPos) arg cases, endPos)

--------------------------------------------------------------------------------------------
-- Cocase
--------------------------------------------------------------------------------------------

termCaseIP :: Parser (CST.TermCaseI, SourcePos)
termCaseIP = do
  startPos <- getSourcePos
  (xt, _) <- xtorNameP
  (bs, _) <- bindingSiteIP
  _ <- rightarrow
  (res, endPos) <- termTopP
  return ((Loc startPos endPos, xt, bs, res), endPos)

cocaseP :: Parser (CST.Term, SourcePos)
cocaseP = do
  startPos <- getSourcePos
  _ <- cocaseKwP
  (cocases, endPos) <- braces ((fst <$> termCaseIP) `sepBy` comma)
  return (CST.Cocase (Loc startPos endPos) cocases, endPos)

--------------------------------------------------------------------------------------------
-- CST-Sugar
--------------------------------------------------------------------------------------------

lambdaP :: Parser (CST.Term, SourcePos)
lambdaP = do
  startPos <- getSourcePos
  _ <- backslash
  bvars <- some $ fst <$> freeVarName
  _ <- rightarrow
  (tm, endPos) <- termTopP
  return (CST.MultiLambda (Loc startPos endPos) bvars tm, endPos)

termParensP :: Parser (CST.Term, SourcePos)
termParensP = do
  startPos <- getSourcePos
  (tm,endPos) <- parens (fst <$> termTopP)
  return (CST.TermParens (Loc startPos endPos) tm, endPos)

-- b  ::= x
--      | n
--      | C(t,...,t)
--      | match t with {...}
--      | comatch {...}
--      | (t)
--      | \x => t
termBotP :: Parser (CST.Term, SourcePos)
termBotP = freeVar <|>
  try (natLitP Structural) <|>
  natLitP Nominal <|>
  xtorP <|>
  xmatchP <|>
  caseofP  <|>
  cocaseP  <|>
  muAbstraction  <|>
  termParensP <|>
  lambdaP

-------------------------------------------------------------------------------------------
-- Middle Parser
-------------------------------------------------------------------------------------------

applicationP :: Parser (CST.Term, SourcePos)
applicationP = do
  startPos <- getSourcePos
  aterms <- some termBotP
  return $ mkApps startPos aterms

mkApps :: SourcePos -> [(CST.Term, SourcePos)] -> (CST.Term, SourcePos)
mkApps _startPos []  = error "Impossible! The `some` parser in applicationP parses at least one element."
mkApps _startPos [x] = x
mkApps startPos ((a1,_):(a2,endPos):as) =
  let
    tm = CST.FunApp (Loc startPos endPos) a1 a2
  in
    mkApps startPos ((tm,endPos):as)


-- m ::= b ... b (n-ary application, left associative)
--     | b
termMiddleP :: Parser (CST.Term, SourcePos)
termMiddleP = applicationP -- applicationP handles the case of 0-ary application

-------------------------------------------------------------------------------------------
-- Top Parser
-------------------------------------------------------------------------------------------

-- | Parses "D(t,..*.,t)"
destructorP :: Parser (XtorName, CST.SubstitutionI, SourcePos)
destructorP = do
  (xt, _) <- xtorNameP
  (substi, endPos) <- substitutionIP
  return (xt, substi, endPos)

destructorChainP :: Parser [(XtorName, CST.SubstitutionI, SourcePos)]
destructorChainP = many (dot >> destructorP)

dtorP :: Parser (CST.Term, SourcePos)
dtorP = do
  startPos <- getSourcePos
  (destructee, endPos) <- termMiddleP
  destructorChain <- destructorChainP
  case destructorChain of
    [] -> return (destructee, endPos)
    (x:xs) -> return (CST.DtorChain startPos destructee (x :| xs), endPos)


-- t ::= m.D(t,...,t). ... .D(t,...,t)
--     | m
termTopP :: Parser (CST.Term, SourcePos)
termTopP = dtorP -- dtorP handles the case with an empty dtor chain.

-------------------------------------------------------------------------------------------
-- Exported Parsers
-------------------------------------------------------------------------------------------

termP :: Parser (CST.Term, SourcePos)
termP = termTopP

commandP :: Parser (CST.Command, SourcePos)
commandP = cstcommandP
