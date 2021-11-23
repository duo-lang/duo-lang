module Parser.Terms
  ( termP
  , commandP
  )where

import Text.Megaparsec hiding (State)


import Parser.Definition
import Parser.Lexer
import Syntax.Terms
import Syntax.CommonTerm
import Utils

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
    numToTerm loc 0 = XtorCall loc PrdRep (MkXtorName ns "Z") (MkSubst [] [])
    numToTerm loc n = XtorCall loc PrdRep (MkXtorName ns "S") (MkSubst [numToTerm loc (n-1)] [])

-- | Parse two lists, the first in parentheses and the second in brackets.
xtorArgsP :: Parser (Substitution Parsed, SourcePos)
xtorArgsP = do
  endPos <- getSourcePos
  (xs, endPos) <- option ([],endPos) (parens   $ (fst <$> (termP PrdRep)) `sepBy` comma)
  (ys, endPos) <- option ([],endPos) (brackets $ (fst <$> (termP CnsRep)) `sepBy` comma)
  return (MkSubst xs ys, endPos)

xtorCall :: NominalStructural -> PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
xtorCall ns pc = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorName ns
  (args, endPos) <- xtorArgsP
  return (XtorCall (Loc startPos endPos) pc xt args, endPos)

--------------------------------------------------------------------------------------------
-- Pattern and copattern matches
--------------------------------------------------------------------------------------------

singleCase :: NominalStructural -> Parser (SCase Parsed, SourcePos)
singleCase ns = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorName ns
  (args,_) <- argListP (fst <$> freeVarName) (fst <$> freeVarName)
  _ <- rightarrow
  (cmd, endPos) <- commandP
  let pmcase = MkSCase { scase_ext = Loc startPos endPos
                       , scase_name = xt
                       , scase_args = fmap Just <$> args
                       , scase_cmd = commandClosing args cmd -- de brujin transformation
                       }
  return (pmcase, endPos)


-- We put the structural pattern match parser before the nominal one, since in the case of an empty match/comatch we want to
-- infer a structural type, not a nominal one.
casesP :: Parser ([SCase Parsed], NominalStructural,SourcePos)
casesP = try structuralCases <|> nominalCases
  where
    structuralCases = do
      (cases, endPos) <- braces ((fst <$> singleCase Structural) `sepBy` comma)
      return (cases, Structural, endPos)
    nominalCases = do
      (cases, endPos) <- braces ((fst <$> singleCase Nominal) `sepBy1` comma)
      -- There must be at least one case for a nominal type to be inferred
      return (cases, Nominal, endPos)

patternMatch :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
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

muAbstraction :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
muAbstraction PrdRep = do
  startPos <- getSourcePos
  _ <- muKwP
  (v, _pos) <- freeVarName
  _ <- dot
  (cmd, endPos) <- commandP
  return (MuAbs (Loc startPos endPos) PrdRep (Just v) (commandClosingSingle CnsRep v cmd), endPos)
muAbstraction CnsRep = do
  startPos <- getSourcePos
  _ <- muKwP
  (v, _pos) <- freeVarName
  _ <- dot
  (cmd, endPos) <- commandP
  return (MuAbs (Loc startPos endPos) CnsRep (Just v) (commandClosingSingle PrdRep v cmd), endPos)

--------------------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------------------

applyCmdP :: Parser (Command Parsed, SourcePos)
applyCmdP = do
  startPos <- getSourcePos
  (prd, _pos) <- termP PrdRep
  _ <- commandSym
  (cns, endPos) <- termP CnsRep
  return (Apply (Loc startPos endPos) prd cns, endPos)

doneCmdP :: Parser (Command Parsed, SourcePos)
doneCmdP = do
  startPos <- getSourcePos
  endPos <- doneKwP
  return (Done (Loc startPos endPos), endPos)

printCmdP :: Parser (Command Parsed, SourcePos)
printCmdP = do
  startPos <- getSourcePos
  _ <- printKwP
  (arg,endPos) <- parens (fst <$> termP PrdRep)
  return (Print (Loc startPos endPos) arg, endPos)

commandP :: Parser (Command Parsed, SourcePos)
commandP =
  try (fst <$> (parens commandP)) <|>
  doneCmdP <|>
  printCmdP <|>
  applyCmdP



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

acaseP :: NominalStructural -> Parser (ACase Parsed)
acaseP ns = do
  startPos <- getSourcePos
  (xt, _) <- xtorName ns
  args <- option [] (fst <$> (parens $ (fst <$> freeVarName) `sepBy` comma))
  _ <- rightarrow
  (res, endPos) <- termTopP PrdRep
  return (MkACase (Loc startPos endPos) xt (Just <$> args) (termClosing (Twice args []) res))

acasesP :: Parser ([ACase Parsed], SourcePos)
acasesP = try structuralCases <|> nominalCases
  where
    structuralCases = braces $ acaseP Structural `sepBy` comma
    nominalCases = braces $ acaseP Nominal `sepBy` comma

matchP :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
matchP CnsRep = empty
matchP PrdRep = do
  startPos <- getSourcePos
  _ <- caseKwP
  (arg, _pos) <- termP PrdRep
  _ <- ofKwP
  (cases, endPos) <- acasesP
  return (Match (Loc startPos endPos) arg cases, endPos)

comatchP :: PrdCnsRep pc -> Parser (Term pc Parsed, SourcePos)
comatchP CnsRep = empty
comatchP PrdRep = do
  startPos <- getSourcePos
  _ <- cocaseKwP
  (cocases, endPos) <- acasesP
  return (Comatch (Loc startPos endPos) cocases, endPos)

-- | Create a lambda abstraction. 
mkLambda :: Loc -> FreeVarName -> Term Prd Parsed -> Term Prd Parsed
mkLambda loc var tm = Comatch loc [MkACase loc (MkXtorName Structural "Ap") [Just var] (termClosing (Twice [var] []) tm)]


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
mkApp loc fun arg = Dtor loc (MkXtorName Structural "Ap") fun [arg]

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

-- | Parses "D(t,...,t)"
destructorP' :: NominalStructural -> Parser (XtorName,[Term Prd Parsed], SourcePos)
destructorP' ns = do
  (xt, endPos) <- xtorName ns
  (args, endPos) <- option ([], endPos) (parens $ (fst <$> termTopP PrdRep) `sepBy` comma)
  return (xt, args, endPos)

destructorP :: Parser (XtorName,[Term Prd Parsed], SourcePos)
destructorP = destructorP' Structural <|> destructorP' Nominal

destructorChainP :: Parser [(XtorName,[Term Prd Parsed], SourcePos)]
destructorChainP = many (dot >> destructorP)

mkDtorChain :: SourcePos
            -> (Term Prd Parsed, SourcePos)
            -> [(XtorName,[Term Prd Parsed], SourcePos)]
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


