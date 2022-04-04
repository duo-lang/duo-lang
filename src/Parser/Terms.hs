module Parser.Terms
  ( termP
  , commandP
  )where

import Data.Bifunctor (first)
import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (keys)
import Text.Megaparsec hiding (State)

import Parser.Common
import Parser.Definition
import Parser.Lexer
import Syntax.CST.Terms qualified as CST
import Syntax.Common
import Utils

--------------------------------------------------------------------------------------------
-- Substitutions and implicit substitutions
--------------------------------------------------------------------------------------------

mkTerm :: (PrdCns, CST.Term) -> CST.PrdCnsTerm
mkTerm (Prd, tm) = CST.PrdTerm tm
mkTerm (Cns, tm) = CST.CnsTerm tm

-- | Parse a substitution, consisting of lists of producers and consumers.
-- E.g.: "[cns,cns](prd)[cns](prd,prd)"
substitutionP :: Parser (CST.Substitution, SourcePos)
substitutionP = first (fmap mkTerm) <$> argListsP False (fst <$> termTopP)

substitutionIP :: Parser (CST.SubstitutionI, SourcePos)
substitutionIP = do
  ((subst1,(),subst2), endPos) <- argListsIP Cns (fst <$> termTopP)
  return ((mkTerm <$> subst1, Prd, mkTerm <$> subst2), endPos)

--------------------------------------------------------------------------------------------
-- Binding sites and implicit binding sites
--------------------------------------------------------------------------------------------

bindingSiteP :: Parser (CST.BindingSite, SourcePos)
bindingSiteP = argListsP False (fst <$> freeVarNameP)

bindingSiteIP :: Parser (CST.BindingSiteI, SourcePos)
bindingSiteIP = argListsIP Cns (fst <$> freeVarNameP)

--------------------------------------------------------------------------------------------
-- Free Variables and Xtors
--------------------------------------------------------------------------------------------

freeVar :: Parser (CST.Term, SourcePos)
freeVar = do
  startPos <- getSourcePos
  (v, endPos) <- freeVarNameP
  return (CST.Var (Loc startPos endPos) v, endPos)

xtorP :: Parser (CST.Term, SourcePos)
xtorP = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorNameP
  (subst, endPos) <- substitutionP
  return (CST.Xtor (Loc startPos endPos) xt subst, endPos)

--------------------------------------------------------------------------------------------
-- Literals and primitives
--------------------------------------------------------------------------------------------

natLitP :: NominalStructural -> Parser (CST.Term, SourcePos)
natLitP ns = do
  startPos <- getSourcePos
  () <- checkTick ns
  (num, endPos) <- natP <* notFollowedBy (symbolP SymHash)
  return (CST.NatLit (Loc startPos endPos) ns num, endPos)

f64LitP :: Parser (CST.Term, SourcePos)
f64LitP = do
  startPos <- getSourcePos
  (double, endPos) <- try $ do
    (double,_) <- floatP
    endPos <- keywordP KwF64
    pure (double, endPos)
  pure (CST.PrimLitF64 (Loc startPos endPos) double, endPos)

i64LitP :: Parser (CST.Term, SourcePos)
i64LitP = do
  startPos <- getSourcePos
  (int, endPos) <- try $ do
    (int,_) <- intP
    endPos <- keywordP KwI64
    pure (int, endPos)
  pure (CST.PrimLitI64 (Loc startPos endPos) int, endPos)

--------------------------------------------------------------------------------------------
-- Mu abstractions
--------------------------------------------------------------------------------------------

muAbstraction :: Parser (CST.Term, SourcePos)
muAbstraction = do
  startPos <- getSourcePos
  _ <- keywordP KwMu
  (v, _pos) <- freeVarNameP
  _ <- symbolP SymDot
  (cmd, endPos) <- cstcommandP
  return (CST.MuAbs (Loc startPos endPos) v cmd, endPos)

--------------------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------------------

applyCmdP :: Parser (CST.Command, SourcePos)
applyCmdP = do
  startPos <- getSourcePos
  (prd, _pos) <- try (termTopP <* symbolP SymCommand)
  (cns, endPos) <- termTopP
  return (CST.Apply (Loc startPos endPos) prd cns, endPos)

exitSuccessCmdP :: Parser (CST.Command, SourcePos)
exitSuccessCmdP = do
  startPos <- getSourcePos
  endPos <- keywordP KwExitSuccess
  return (CST.ExitSuccess (Loc startPos endPos), endPos)

exitFailureCmdP :: Parser (CST.Command, SourcePos)
exitFailureCmdP = do
  startPos <- getSourcePos
  endPos <- keywordP KwExitFailure
  return (CST.ExitFailure (Loc startPos endPos), endPos)

printCmdP :: Parser (CST.Command, SourcePos)
printCmdP = do
  startPos <- getSourcePos
  _ <- keywordP KwPrint
  (arg,_) <- parens (fst <$> termTopP)
  _ <- symbolP SymSemi
  (cmd, endPos) <- cstcommandP
  return (CST.Print (Loc startPos endPos) arg cmd, endPos)

readCmdP :: Parser (CST.Command, SourcePos)
readCmdP = do
  startPos <- getSourcePos
  _ <- keywordP KwRead
  (arg,endPos) <- brackets (fst <$> termTopP)
  return (CST.Read (Loc startPos endPos) arg, endPos)

commandVar :: Parser (CST.Command, SourcePos)
commandVar = do
  startPos <- getSourcePos
  (nm, endPos) <- freeVarNameP
  return (CST.Jump (Loc startPos endPos) nm, endPos)

commandParensP :: Parser (CST.Command, SourcePos)
commandParensP = do
  startPos <- getSourcePos
  ((cmd,_), endPos) <- parens cstcommandP
  return (CST.CommandParens (Loc startPos endPos) cmd, endPos)

primitiveCmdP :: Parser (CST.Command, SourcePos)
primitiveCmdP = do
  startPos <- getSourcePos
  (pt, op, _) <- asum (uncurry primOpKeywordP <$> keys primOps)
  (subst, endPos) <- substitutionP
  pure (CST.PrimOp (Loc startPos endPos) pt op subst, endPos)

cstcommandP :: Parser (CST.Command, SourcePos)
cstcommandP =
  try commandParensP
  <|> exitSuccessCmdP
  <|> exitFailureCmdP
  <|> printCmdP
  <|> readCmdP
  <|> primitiveCmdP
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

allCaseP :: Parser (CST.Term, SourcePos)
allCaseP = caseP <|> cocaseP

------------------------------------------

caseP :: Parser (CST.Term, SourcePos)
caseP = do
  startPos <- getSourcePos
  _ <- keywordP KwCase
  caseRestP startPos <|> caseRestP' startPos

caseRestP :: SourcePos -> Parser (CST.Term, SourcePos)
caseRestP startPos = do
  (cases, endPos) <- braces ((fst <$> cmdcaseP) `sepBy` symbolP SymComma)
  return (CST.XMatch (Loc startPos endPos) Data cases, endPos)

caseRestP' :: SourcePos -> Parser (CST.Term, SourcePos)
caseRestP' startPos = do
  (arg, _pos) <- termTopP
  _ <- keywordP KwOf
  (cases, endPos) <- braces ((fst <$> termCaseP) `sepBy` symbolP SymComma)
  return (CST.Case (Loc startPos endPos) arg cases, endPos)

------------------------------------------

cocaseP :: Parser (CST.Term, SourcePos)
cocaseP = do
  startPos <- getSourcePos
  _ <- keywordP KwCocase
  try (cocaseRestP startPos) <|> cocaseRestP' startPos

cocaseRestP :: SourcePos -> Parser (CST.Term, SourcePos)
cocaseRestP startPos = do
  (cocases, endPos) <- braces ((fst <$> termCaseIP) `sepBy` symbolP SymComma)
  return (CST.Cocase (Loc startPos endPos) cocases, endPos)

cocaseRestP' :: SourcePos -> Parser (CST.Term, SourcePos)
cocaseRestP' startPos = do
  (cases, endPos) <- braces ((fst <$> cmdcaseP) `sepBy` symbolP SymComma)
  return (CST.XMatch (Loc startPos endPos) Codata cases, endPos)

--------------------------------------------------------------------------------------------
-- XMatches
--------------------------------------------------------------------------------------------

cmdcaseP :: Parser (CST.CommandCase, SourcePos)
cmdcaseP = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorNameP
  (args,_) <- bindingSiteP
  _ <- symbolP SymDoubleRightArrow
  (cmd, endPos) <- cstcommandP
  let pmcase = (Loc startPos endPos, xt, args, cmd)
  return (pmcase, endPos)


--------------------------------------------------------------------------------------------
-- Case-of
--------------------------------------------------------------------------------------------

termCaseP :: Parser (CST.TermCase, SourcePos)
termCaseP = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorNameP
  (args,_) <- bindingSiteP
  _ <- symbolP SymDoubleRightArrow
  (res, endPos) <- termTopP
  let pmcase = (Loc startPos endPos, xt, args, res)
  return (pmcase, endPos)


--------------------------------------------------------------------------------------------
-- Cocase
--------------------------------------------------------------------------------------------

termCaseIP :: Parser (CST.TermCaseI, SourcePos)
termCaseIP = do
  startPos <- getSourcePos
  (xt, _) <- xtorNameP
  (bs, _) <- bindingSiteIP
  _ <- symbolP SymDoubleRightArrow
  (res, endPos) <- termTopP
  return ((Loc startPos endPos, xt, bs, res), endPos)

--------------------------------------------------------------------------------------------
-- CST-Sugar
--------------------------------------------------------------------------------------------

lambdaP :: Parser (CST.Term, SourcePos)
lambdaP = do
  startPos <- getSourcePos
  _ <- symbolP SymBackslash
  bvars <- some $ fst <$> freeVarNameP
  _ <- symbolP SymDoubleRightArrow
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
  i64LitP <|>
  f64LitP <|>
  natLitP Structural <|>
  natLitP Nominal <|>
  xtorP <|>
  allCaseP <|>
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
destructorChainP = many (symbolP SymDot >> destructorP)

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
