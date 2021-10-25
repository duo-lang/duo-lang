module Parser.ATerms ( atermP ) where

import Text.Megaparsec hiding (State)

import Parser.Definition
import Parser.Lexer
import Syntax.CommonTerm
import Syntax.ATerms
import Utils (Loc(..))

-------------------------------------------------------------------------------------------
-- BNF Grammar
-------------------------------------------------------------------------------------------

-- e  ::= e e                              Application                (Syntax Sugar)
--      | e.D(e,...,e)                     Dtor
--      | n                                Natural number literal     (Syntax Sugar)
--      | x                                Variable
--      | C(e,...,e)                       Ctor
--      | match e with { case,...,case }   Pattern match
--      | comatch { case,...,case }        Copattern match
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

fvarP :: Parser (ATerm Loc FreeVarName, SourcePos)
fvarP = do
  startPos <- getSourcePos
  (fv, endPos) <- freeVarName
  return (FVar (Loc startPos endPos) fv, endPos)

numLitP :: Parser (ATerm Loc bs, SourcePos)
numLitP = do
  startPos <- getSourcePos
  (num, endPos) <- numP
  return (numToTerm  (Loc startPos endPos) num, endPos)
  where
    numToTerm :: Loc -> Int -> ATerm Loc bs
    numToTerm loc 0 = Ctor loc (MkXtorName Nominal "Z") []
    numToTerm loc n = Ctor loc (MkXtorName Nominal "S") [numToTerm loc (n-1)]

ctorP :: NominalStructural -> Parser (ATerm Loc FreeVarName, SourcePos)
ctorP ns = do
  startPos <- getSourcePos
  (xt, endPos) <- xtorName ns
  (args, endPos) <- option ([], endPos) (parens $ (fst <$> atermP) `sepBy` comma)
  return (Ctor (Loc startPos endPos) xt args, endPos)

acaseP :: NominalStructural -> Parser (ACase Loc FreeVarName)
acaseP ns = do
  startPos <- getSourcePos
  (xt, _) <- xtorName ns
  args <- option [] (fst <$> (parens $ (fst <$> freeVarName) `sepBy` comma))
  _ <- rightarrow
  (res, endPos) <- atermP
  return (MkACase (Loc startPos endPos) xt args (atermClosing args res))

acasesP :: Parser ([ACase Loc FreeVarName], SourcePos)
acasesP = try structuralCases <|> nominalCases
  where
    structuralCases = braces $ acaseP Structural `sepBy` comma
    nominalCases = braces $ acaseP Nominal `sepBy` comma

matchP :: Parser (ATerm Loc FreeVarName, SourcePos)
matchP = do
  startPos <- getSourcePos
  _ <- matchKwP
  (arg, _pos) <- atermP
  _ <- withKwP
  (cases, endPos) <- acasesP
  return (Match (Loc startPos endPos) arg cases, endPos)

comatchP :: Parser (ATerm Loc FreeVarName, SourcePos)
comatchP = do
  startPos <- getSourcePos
  _ <- comatchKwP
  (cocases, endPos) <- acasesP
  return (Comatch (Loc startPos endPos) cocases, endPos)

-- | Create a lambda abstraction. 
mkLambda :: Loc -> FreeVarName -> ATerm Loc FreeVarName -> ATerm Loc FreeVarName
mkLambda loc var tm = Comatch loc [MkACase loc (MkXtorName Structural "Ap") [var] (atermClosing [var] tm)]


lambdaP :: Parser (ATerm Loc FreeVarName, SourcePos)
lambdaP = do
  startPos <- getSourcePos
  _ <- backslash
  bvar <- freeVarName
  _ <- rightarrow 
  (tm, endPos) <- atermP
  let res = mkLambda (Loc startPos endPos) (fst bvar) tm
  return (res, endPos)

-- b  ::= x
--      | n
--      | C(t,...,t)
--      | match t with {...}
--      | comatch {...}
--      | (t)
--      | \x => t
atermBotP :: Parser (ATerm Loc FreeVarName, SourcePos)
atermBotP =
  fvarP <|>
  numLitP <|>
  ctorP Structural <|>
  ctorP Nominal <|>
  matchP <|>
  comatchP <|>
  parens (fst <$> atermTopP) <|>
  lambdaP

-------------------------------------------------------------------------------------------
-- Middle Parser
-------------------------------------------------------------------------------------------


-- | Create an application.
mkApp :: Loc -> ATerm Loc FreeVarName -> ATerm Loc FreeVarName -> ATerm Loc FreeVarName
mkApp loc fun arg = Dtor loc (MkXtorName Structural "Ap") fun [arg]

-- TODO replace by nonempty
mkApps :: [ATerm Loc FreeVarName] -> ATerm Loc FreeVarName 
mkApps = undefined -- foldl mkApp

applicationP :: Parser (ATerm Loc FreeVarName, SourcePos)
applicationP = do
  a <- many atermBotP
  startPos <- getSourcePos
  (fun,_) <- atermP
  (arg, endPos) <- atermP
  let app = mkApp (Loc startPos endPos) fun arg
  return (app, endPos)


-- m ::= b ... b (n-ary application, left associative)
--     | b
atermMiddleP :: Parser (ATerm Loc FreeVarName, SourcePos)
atermMiddleP = applicationP -- applicationP handles the case of 0-ary application

-------------------------------------------------------------------------------------------
-- Top Parser
-------------------------------------------------------------------------------------------




-- | Parses "D(t,...,t)"
destructorP' :: NominalStructural -> Parser (XtorName,[ATerm Loc FreeVarName], SourcePos)
destructorP' ns = do
  (xt, endPos) <- xtorName ns
  (args, endPos) <- option ([], endPos) (parens $ (fst <$> atermP) `sepBy` comma)
  return (xt, args, endPos)

destructorP :: Parser (XtorName,[ATerm Loc FreeVarName], SourcePos)
destructorP = destructorP' Structural <|> destructorP' Nominal

destructorChainP :: Parser [(XtorName,[ATerm Loc FreeVarName], SourcePos)]
destructorChainP = many (dot >> destructorP)

mkDtorChain :: ATerm Loc FreeVarName -> [(XtorName,[ATerm Loc FreeVarName], SourcePos)] -> ATerm Loc FreeVarName
mkDtorChain destructee destructorChain = undefined 

dtorP :: Parser (ATerm Loc FreeVarName, SourcePos)
dtorP = do
  startPos <- getSourcePos
  (destructee,_pos) <- atermMiddleP
  destructorChain <- destructorChainP
  return  (mkDtorChain destructee destructorChain, undefined)


-- t ::= m.D(t,...,t). ... .D(t,...,t)
--     | m
atermTopP :: Parser (ATerm Loc FreeVarName, SourcePos)
atermTopP = dtorP -- dtorP handles the case with an empty dtor chain.


-------------------------------------------------------------------------------------------
-- Exported Parsers
-------------------------------------------------------------------------------------------

atermP :: Parser (ATerm Loc FreeVarName, SourcePos)
atermP = atermTopP