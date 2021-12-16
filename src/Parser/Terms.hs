module Parser.Terms
  ( termP
  , commandP
  )where

import Data.Bifunctor

import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.Terms
import Syntax.CommonTerm
import Utils

--------------------------------------------------------------------------------------------
-- Substitutions
--------------------------------------------------------------------------------------------

-- | Parse a non-empty list of producers in parentheses.
-- E.g. "(prd,prd,prd)""
prdSubstPart :: Parser (Substitution Parsed, SourcePos)
prdSubstPart = parens   $ (PrdTerm . fst <$> termP PrdRep) `sepBy` comma

-- | Parse a non-empty list of consumers in brackets.
-- E.g. "[cns,cns,cns]"
cnsSubstPart :: Parser (Substitution Parsed, SourcePos)
cnsSubstPart = brackets $ (CnsTerm . fst <$> termP CnsRep) `sepBy` comma


-- | Parse a substitution, consisting of lists of producers and consumers.
-- E.g.: "[cns,cns](prd)[cns](prd,prd)"
substitutionP :: Parser (Substitution Parsed, SourcePos)
substitutionP = do
  endPos <- getSourcePos
  xs <- many (prdSubstPart <|> try cnsSubstPart)
  case xs of
    [] -> return ([], endPos)
    xs -> return (concat (fst <$> xs), snd (last xs))

--------------------------------------------------------------------------------------------
-- Free Variables, Literals and Xtors
--------------------------------------------------------------------------------------------

freeVar :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
freeVar pc = do
  startPos <- getSourcePos
  (v, endPos) <- freeVarName
  return (FreeVar (Loc startPos endPos) pc v, endPos)

numLitP :: NominalStructural -> PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
numLitP _ CnsRep = empty
numLitP ns PrdRep = do
  startPos <- getSourcePos
  () <- checkTick ns
  (num, endPos) <- numP
  return (numToTerm (Loc startPos endPos) num, endPos)
  where
    numToTerm :: Loc -> Int -> Term Prd Parsed
    numToTerm loc 0 = XtorCall loc PrdRep (MkXtorName ns "Z") []
    numToTerm loc n = XtorCall loc PrdRep (MkXtorName ns "S") [PrdTerm $ numToTerm loc (n-1)]

xtorCall :: NominalStructural -> PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
xtorCall ns pc = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorName ns
  (subst, endPos) <- substitutionP
  return (XtorCall (Loc startPos endPos) pc xt subst, endPos)

--------------------------------------------------------------------------------------------
-- Argument lists
--------------------------------------------------------------------------------------------

-- | Parse a non-empty list of producer arguments in parentheses.
-- E.g. "(prd,prd,prd)""
prdArgList :: Parser a -> Parser ([(PrdCns, a)], SourcePos)
prdArgList p = parens  $ ((,) Prd <$> p) `sepBy` comma

-- | Parse a non-empty list of consumer arguments in brackets.
-- E.g. "[cns,cns,cns]"
cnsArgList :: Parser a -> Parser ([(PrdCns,a)], SourcePos)
cnsArgList p = brackets $ ((,) Cns <$> p) `sepBy` comma

-- | Parse a sequence of produer/consumer argument lists
argListsP ::  Parser a -> Parser a ->  Parser ([(PrdCns,a)], SourcePos)
argListsP p q = do
  endPos <- getSourcePos
  xs <- many (prdArgList p <|> try (cnsArgList q))
  case xs of
    [] -> return ([], endPos)
    xs -> return (concat (fst <$> xs), snd (last xs))

--------------------------------------------------------------------------------------------
-- Mu abstractions
--------------------------------------------------------------------------------------------

muAbstraction :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
muAbstraction PrdRep = do
  startPos <- getSourcePos
  _ <- muKwP
  (v, _pos) <- freeVarName
  _ <- dot
  (cmd, endPos) <- commandP
  return (MuAbs (Loc startPos endPos) PrdRep (Just v) (commandClosing [(Cns,v)] cmd), endPos)
muAbstraction CnsRep = do
  startPos <- getSourcePos
  _ <- muKwP
  (v, _pos) <- freeVarName
  _ <- dot
  (cmd, endPos) <- commandP
  return (MuAbs (Loc startPos endPos) CnsRep (Just v) (commandClosing [(Prd,v)] cmd), endPos)

--------------------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------------------

applyCmdP :: Parser (Command Parsed, SourcePos)
applyCmdP = do
  startPos <- getSourcePos
  (prd, _pos) <- try (termP PrdRep <* commandSym)
  (cns, endPos) <- termP CnsRep
  return (Apply (Loc startPos endPos) Nothing prd cns, endPos)

doneCmdP :: Parser (Command Parsed, SourcePos)
doneCmdP = do
  startPos <- getSourcePos
  endPos <- doneKwP
  return (Done (Loc startPos endPos), endPos)

printCmdP :: Parser (Command Parsed, SourcePos)
printCmdP = do
  startPos <- getSourcePos
  _ <- printKwP
  (arg,_) <- parens (fst <$> termP PrdRep)
  _ <- semi
  (cmd, endPos) <- commandP
  return (Print (Loc startPos endPos) arg cmd, endPos)

readCmdP :: Parser (Command Parsed, SourcePos)
readCmdP = do
  startPos <- getSourcePos
  _ <- readKwP
  (arg,endPos) <- brackets (fst <$> termP CnsRep)
  return (Read (Loc startPos endPos) arg, endPos)

commandVar :: Parser (Command Parsed, SourcePos)
commandVar = do
  startPos <- getSourcePos
  (nm, endPos) <- freeVarName
  return (Call (Loc startPos endPos) nm, endPos)

commandP :: Parser (Command Parsed, SourcePos)
commandP =
  try (fst <$> (parens commandP))
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
-- Pattern and copattern matches
--------------------------------------------------------------------------------------------

cmdcaseP :: NominalStructural -> Parser (CmdCase Parsed, SourcePos)
cmdcaseP ns = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorName ns
  (args,_) <- argListP (fst <$> freeVarName) (fst <$> freeVarName)
  _ <- rightarrow
  (cmd, endPos) <- commandP
  let pmcase = MkCmdCase { cmdcase_ext = Loc startPos endPos
                         , cmdcase_name = xt
                         , cmdcase_args = (\(pc,fv) -> (pc, Just fv)) <$> args
                         , cmdcase_cmd = commandClosing args cmd -- de brujin transformation
                         }
  return (pmcase, endPos)

termCaseP :: NominalStructural -> Parser (TermCase Parsed, SourcePos)
termCaseP ns = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorName ns
  (args,_) <- argListP (fst <$> freeVarName) (fst <$> freeVarName)
  _ <- rightarrow
  (res, endPos) <- termTopP PrdRep
  let pmcase = MkTermCase { tmcase_ext = Loc startPos endPos
                          , tmcase_name = xt
                          , tmcase_args = (\(pc,fv) -> (pc, Just fv)) <$> args
                          , tmcase_term = termClosing args res
                          }
  return (pmcase, endPos)

termCaseIP :: NominalStructural -> Parser (TermCaseI Parsed, SourcePos)
termCaseIP ns = do
  startPos <- getSourcePos
  (xt, _) <- xtorName ns
  (as1, _) <- argListsP (fst <$> freeVarName) (fst <$> freeVarName)
  _ <- brackets implicitSym
  (as2, _) <- argListsP (fst <$> freeVarName) (fst <$> freeVarName)
  _ <- rightarrow
  (res, endPos) <- termTopP PrdRep
  let pmcase = MkTermCaseI { tmcasei_ext = Loc startPos endPos
                           , tmcasei_name = xt
                           , tmcasei_args = (second Just <$> as1, (), second Just <$> as2)
                           -- HACK: We want to ensure that the implicit argument gets the intuitive De-Bruijn index.
                           -- termClosing doesn't support implicit arguments yet. We can emulate it for now by passing
                           -- a string that cannot be parsed as a variable (e.g. *).
                           , tmcasei_term = termClosing (as1 ++ [(Cns, "*")] ++ as2) res
                           }
  return (pmcase, endPos)

-- We put the structural pattern match parser before the nominal one, since in the case of an empty match/comatch we want to
-- infer a structural type, not a nominal one.
cmdcasesP :: Parser ([CmdCase Parsed], NominalStructural,SourcePos)
cmdcasesP = try structuralCases <|> nominalCases
  where
    structuralCases = do
      (cases, endPos) <- braces ((fst <$> cmdcaseP Structural) `sepBy` comma)
      return (cases, Structural, endPos)
    nominalCases = do
      (cases, endPos) <- braces ((fst <$> cmdcaseP Nominal) `sepBy1` comma)
      -- There must be at least one case for a nominal type to be inferred
      return (cases, Nominal, endPos)

termCasesP :: Parser ([TermCase Parsed], NominalStructural , SourcePos)
termCasesP = try structuralCases <|> nominalCases
  where
    structuralCases = do
      (cases, endPos) <- braces ((fst <$> termCaseP Structural) `sepBy` comma)
      return (cases, Structural, endPos)
    nominalCases = do
      (cases,endPos) <- braces ((fst <$> termCaseP Nominal) `sepBy` comma)
      return (cases, Nominal, endPos)

termCasesIP :: Parser ([TermCaseI Parsed], NominalStructural , SourcePos)
termCasesIP = try structuralCases <|> nominalCases
  where
    structuralCases = do
      (cases, endPos) <- braces ((fst <$> termCaseIP Structural) `sepBy` comma)
      return (cases, Structural, endPos)
    nominalCases = do
      (cases,endPos) <- braces ((fst <$> termCaseIP Nominal) `sepBy` comma)
      return (cases, Nominal, endPos)

patternMatch :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
patternMatch PrdRep = do
  startPos <- getSourcePos
  _ <- comatchKwP
  (cases,ns, endPos) <- cmdcasesP
  return (XMatch (Loc startPos endPos) PrdRep ns cases, endPos)
patternMatch CnsRep = do
  startPos <- getSourcePos
  _ <- matchKwP
  (cases,ns,endPos) <- cmdcasesP
  return (XMatch (Loc startPos endPos) CnsRep ns cases, endPos)

matchP :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
matchP CnsRep = empty
matchP PrdRep = do
  startPos <- getSourcePos
  _ <- caseKwP
  (arg, _pos) <- termP PrdRep
  _ <- ofKwP
  (cases, ns, endPos) <- termCasesP
  return (Match (Loc startPos endPos) ns arg cases, endPos)

comatchP :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
comatchP CnsRep = empty
comatchP PrdRep = do
  startPos <- getSourcePos
  _ <- cocaseKwP
  (cocases, ns, endPos) <- termCasesIP
  return (Comatch (Loc startPos endPos) ns cocases, endPos)

-- | Create a lambda abstraction.
mkLambda :: Loc -> FreeVarName -> Term Prd Parsed -> Term Prd Parsed
mkLambda loc var tm = Comatch loc Structural
  [
    MkTermCaseI loc (MkXtorName Structural "Ap")
                ([(Prd, Just var)], (), [])
                (termClosing [(Prd, var)] tm)
  ]

lambdaP :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
lambdaP CnsRep = empty
lambdaP PrdRep = do
  startPos <- getSourcePos
  _ <- backslash
  bvar <- freeVarName
  _ <- rightarrow
  (tm, endPos) <- termTopP PrdRep
  let res = mkLambda (Loc startPos endPos) (fst bvar) tm
  return (res, endPos)

-- b  ::= x
--      | n
--      | C(t,...,t)
--      | match t with {...}
--      | comatch {...}
--      | (t)
--      | \x => t
termBotP :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
termBotP rep = freeVar rep <|>
  try (numLitP Structural rep) <|>
  try (numLitP Nominal rep) <|>
  xtorCall Structural rep <|>
  xtorCall Nominal rep <|>
  patternMatch rep <|>
  matchP rep <|>
  comatchP rep <|>
  muAbstraction rep <|>
  parens (fst <$> termTopP rep) <|>
  lambdaP rep

-------------------------------------------------------------------------------------------
-- Middle Parser
-------------------------------------------------------------------------------------------


-- | Create an application.
mkApp :: Loc -> Term Prd Parsed -> Term Prd Parsed -> Term Prd Parsed
mkApp loc fun arg = Dtor loc (MkXtorName Structural "Ap") fun ([PrdTerm arg],PrdRep,[])

mkApps :: SourcePos -> [(Term Prd Parsed, SourcePos)] -> (Term Prd Parsed, SourcePos)
mkApps _startPos []  = error "Impossible! The `some` parser in applicationP parses at least one element."
mkApps _startPos [x] = x
mkApps startPos ((a1,_):(a2,endPos):as) =
  let
    tm = mkApp (Loc startPos endPos) a1 a2
  in
    mkApps startPos ((tm,endPos):as)


applicationP :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
applicationP CnsRep = termBotP CnsRep
applicationP PrdRep = do
  startPos <- getSourcePos
  aterms <- some (termBotP PrdRep)
  return $ mkApps startPos aterms


-- m ::= b ... b (n-ary application, left associative)
--     | b
termMiddleP :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
termMiddleP = applicationP -- applicationP handles the case of 0-ary application

-------------------------------------------------------------------------------------------
-- Top Parser
-------------------------------------------------------------------------------------------

-- | Parses "D(t,..*.,t)"
destructorP' :: NominalStructural -> Parser (XtorName, SubstitutionI Parsed Prd, SourcePos)
destructorP' ns = do
  (xt, _) <- xtorName ns
  (subst1, _) <- substitutionP
  _ <- brackets implicitSym
  (subst2, endPos) <- substitutionP
  return (xt, (subst1,PrdRep,subst2), endPos)

destructorP :: Parser (XtorName, SubstitutionI Parsed Prd, SourcePos)
destructorP = destructorP' Structural <|> destructorP' Nominal

destructorChainP :: Parser [(XtorName, SubstitutionI Parsed Prd, SourcePos)]
destructorChainP = many (dot >> destructorP)

mkDtorChain :: SourcePos
            -> (Term Prd Parsed, SourcePos)
            -> [(XtorName, SubstitutionI Parsed Prd, SourcePos)]
            -> (Term Prd Parsed, SourcePos)
mkDtorChain _ destructee [] = destructee
mkDtorChain startPos (destructee,_)((xt,args,endPos):dts) =
  let
    loc = Loc startPos endPos
    tm :: Term Prd Parsed = Dtor loc xt destructee args
  in
    mkDtorChain startPos (tm, endPos) dts

dtorP :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
dtorP CnsRep = termMiddleP CnsRep
dtorP PrdRep = do
  startPos <- getSourcePos
  destructee <- termMiddleP PrdRep
  destructorChain <- destructorChainP
  return $ mkDtorChain startPos destructee destructorChain


-- t ::= m.D(t,...,t). ... .D(t,...,t)
--     | m
termTopP :: PrdCnsRep pc ->  Parser (Term pc Parsed, SourcePos)
termTopP = dtorP -- dtorP handles the case with an empty dtor chain.

-------------------------------------------------------------------------------------------
-- Exported Parsers
-------------------------------------------------------------------------------------------

termP :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
termP = termTopP


