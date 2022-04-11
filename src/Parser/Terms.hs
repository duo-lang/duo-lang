module Parser.Terms
  ( termP)where

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
import Debug.Trace

--------------------------------------------------------------------------------------------
-- Substitutions and implicit substitutions
--------------------------------------------------------------------------------------------

mkTerm :: (PrdCns, CST.Term) -> CST.PrdCnsTerm
mkTerm (Prd, tm) = CST.PrdTerm tm
mkTerm (Cns, tm) = CST.CnsTerm tm

-- | Parse a substitution,
-- E.g.: "(t1,t2,t3)"
substitutionP :: Parser ([CST.Term], SourcePos)
substitutionP = do 
     s <- map fst <$> parens  (fst <$> termTopP) `sepBy` symbolP SymComma
     pos <- getSourcePos
     return (s,pos) 

termOrStarP :: Parser (CST.TermOrStar, SourcePos)
termOrStarP = ((\s -> (CST.ToSStar,s)) <$> symbolP SymImplicit) <|> (first CST.ToSTerm <$> termTopP)


substitutionIP :: Parser ([CST.TermOrStar], SourcePos)
substitutionIP = do
     s <- map fst <$> parens  (fst <$> termOrStarP) `sepBy` symbolP SymComma
     pos <- getSourcePos
     return (s,pos) 


--------------------------------------------------------------------------------------------
-- Binding sites and implicit binding sites
--------------------------------------------------------------------------------------------

bindingP :: Parser (CST.FVOrStar , SourcePos)
bindingP = do 
     loc <- symbolP SymImplicit ;  return (CST.FoSStar ,loc)  
        <|> first CST.FoSFV <$> freeVarNameP


bindingSiteP :: Parser (CST.BindingSite, SourcePos)
bindingSiteP = do
  s <- map fst <$> parens  (fst <$> bindingP) `sepBy` symbolP SymComma
  endPos <- getSourcePos
  return (s,endPos) 

--bindingSiteIP :: Parser (CST.BindingSiteI, SourcePos)
--bindingSiteIP = argListsIP Cns (fst <$> freeVarNameP)


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
  (subst, _) <- substitutionP
  afterSemi <- optional $ fst <$> do 
    _ <- symbolP SymSemi 
    termTopP
  endPos <- getSourcePos   
  return (CST.XtorSemi (Loc startPos endPos) xt subst afterSemi, endPos)


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
  (cmd, endPos) <- termTopP
  return (CST.MuAbs (Loc startPos endPos) v cmd, endPos)


--------------------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------------------

applyCmdP :: Parser (CST.Term, SourcePos)
applyCmdP = do
  startPos <- getSourcePos
  (prd, _pos) <- try (termTopP <* symbolP SymCommand)
  (cns, endPos) <- termTopP
  return (CST.Apply (Loc startPos endPos) prd cns, endPos)

exitSuccessCmdP :: Parser (CST.Term, SourcePos)
exitSuccessCmdP = do
  startPos <- getSourcePos
  endPos <- keywordP KwExitSuccess
  return (CST.PrimCmdTerm $ CST.ExitSuccess (Loc startPos endPos), endPos)

exitFailureCmdP :: Parser (CST.Term, SourcePos)
exitFailureCmdP = do
  startPos <- getSourcePos
  endPos <- keywordP KwExitFailure
  return (CST.PrimCmdTerm $ CST.ExitFailure (Loc startPos endPos), endPos)

printCmdP :: Parser (CST.Term, SourcePos)
printCmdP = do
  startPos <- getSourcePos
  _ <- keywordP KwPrint
  (arg,_) <- parens (fst <$> termTopP)
  _ <- symbolP SymSemi
  (cmd, endPos) <- termTopP
  return (CST.PrimCmdTerm $ CST.Print (Loc startPos endPos) arg cmd, endPos)

readCmdP :: Parser (CST.Term, SourcePos)
readCmdP = do
  startPos <- getSourcePos
  _ <- keywordP KwRead
  (arg,endPos) <- brackets (fst <$> termTopP)
  return (CST.PrimCmdTerm $ CST.Read (Loc startPos endPos) arg, endPos)

primitiveCmdP :: Parser (CST.Term, SourcePos)
primitiveCmdP = do
  startPos <- getSourcePos
  (pt, op, _) <- asum (uncurry primOpKeywordP <$> keys primOps)
  (subst, endPos) <- substitutionP
  pure (CST.PrimCmdTerm $ CST.PrimOp (Loc startPos endPos) pt op subst, endPos)




-------------------------------------------------------------------------------------------
-- BNF Grammar
-------------------------------------------------------------------------------------------
--
-- Square brackets [] are part of the grammar syntax and denote optional parts of a production

-- primcmd ::=  Exit | ExitFailure | Print(t) | Read(t) | Prim(..)

-- e  ::= 
--      | primcmd
--      | e e                              Application                (Syntax Sugar)
--      | e.D(e,...,e)                     Dtor
--      | n                                Natural number literal     (Syntax Sugar)
--      | x                                Variable
--      | C(e,...,e)                       Ctor
--      | case { cse,...,cse }    
--      | case e { cse,...,cse }    
--      | cocase { cse,...,cse }    
--      | cocase e { cse,...,cse }    
--      | (e)                              Parenthesized expression
--      | \x => e                          Lambda abstraction         (Syntax sugar)
--      | e >> e                           Command / Cut
--      | C(e,...,e) ; e                   Semicolon sugar
--
-- cse ::= X(v,...,v)[{v}] => e
-- v   ::= x | *

-- This ambiguous grammar can be disambiguated into the following set of grammars,
-- with abbreviations t(top), m(middle), b(bottom)

-- b  ::= x
--      | primcmd 
--      | n
--      | C(t,...,t)[{t}] [ ; t]
--      | case { cse,...,cse }    
--      | case t { cse,...,cse }    
--      | cocase { cse,...,cse }    
--      | cocase t { cse,...,cse }    
--      | (t)
--      | \x => t
--
-- m ::= b ... b (n-ary application, left associative, n >= 1)
--     | b
--
-- t ::= m.D(t,...,t). ... .D(t,...,t) (n-ary destructor application, n >= 1)
--     | m >> m
--     | m
-- 



-------------------------------------------------------------------------------------------
-- Bottom Parser
-------------------------------------------------------------------------------------------


------------------------------------------
datacodataP :: Parser (DataCodata, SourcePos)
datacodataP =  (\s -> (Data,s)) <$> keywordP KwCase 
           <|> (\s -> (Codata,s)) <$> keywordP KwCocase 
------------------------------------------

caseP :: Parser (CST.Term, SourcePos)
caseP = trace "caseP" $ do
  startPos <- getSourcePos
  (dc,_) <- trace "caseP1" $ datacodataP 
  caseRestP dc startPos <|> caseRestP' dc startPos

caseRestP :: DataCodata -> SourcePos -> Parser (CST.Term, SourcePos)
caseRestP dc startPos = do
  (cases, endPos) <- braces ((fst <$> termCaseP) `sepBy` symbolP SymComma)
  return (CST.XCase (Loc startPos endPos) dc Nothing cases, endPos)

caseRestP' :: DataCodata -> SourcePos -> Parser (CST.Term, SourcePos)
caseRestP' dc startPos = do
  (arg, _pos) <- termTopP
  _ <- keywordP KwOf
  (cases, endPos) <- braces ((fst <$> termCaseP) `sepBy` symbolP SymComma)
  return (CST.XCase (Loc startPos endPos) dc (Just arg) cases, endPos)


termCaseP :: Parser (CST.TermCase, SourcePos)
termCaseP = trace "termCaseP"  $ do
  startPos <- getSourcePos
  (xt, _pos) <- xtorNameP
  (args,_) <- bindingSiteP
  _ <- symbolP SymDoubleRightArrow
  (t, endPos) <- termTopP 
  let pmcase = CST.MkTermCase { tmcase_ext  = Loc startPos endPos
                             , tmcase_name = xt
                             , tmcase_args = args
                             , tmcase_term  = t }
  return (pmcase, endPos)



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
termBotP = trace "termBotP" $ freeVar <|>
  i64LitP <|>
  f64LitP <|>
  natLitP Structural <|>
  natLitP Nominal <|>
  xtorP <|>
  caseP <|>
  muAbstraction  <|>
  termParensP <|>
  lambdaP <|>
  primitiveCmdP <|>
  readCmdP <|>
  printCmdP <|>
  exitFailureCmdP <|>
  exitSuccessCmdP


-------------------------------------------------------------------------------------------
-- Middle Parser
-------------------------------------------------------------------------------------------

applicationP :: Parser (CST.Term, SourcePos)
applicationP = trace "applicationP" $do
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
termMiddleP = trace "termMiddleP" $ applicationP -- applicationP handles the case of 0-ary application

-------------------------------------------------------------------------------------------
-- Top Parser
-------------------------------------------------------------------------------------------

-- | Parses "D(t,..*.,t)"
destructorP :: Parser (XtorName, [CST.TermOrStar], SourcePos)
destructorP = do
  (xt, _) <- xtorNameP
  (substi, endPos) <- substitutionIP
  return (xt, substi, endPos)

destructorChainP :: Parser [(XtorName, [CST.TermOrStar], SourcePos)]
destructorChainP = many (symbolP SymDot >> destructorP)

dtorP :: Parser (CST.Term, SourcePos)
dtorP = trace "dtorP" $ do
  startPos <- getSourcePos
  (destructee, endPos) <- termMiddleP
  destructorChain <- destructorChainP
  case destructorChain of
    [] -> return (destructee, endPos)
    (x:xs) -> return (CST.DtorChain startPos destructee (x :| xs), endPos)

termTopP :: Parser (CST.Term, SourcePos)
termTopP = do
             _ <- trace "termTopP" $ return () 
             dtorP <|> applyCmdP-- dtorP handles the case with an empty dtor chain.
        


-------------------------------------------------------------------------------------------
-- Exported Parsers
-------------------------------------------------------------------------------------------

termP :: Parser (CST.Term, SourcePos)
termP = termTopP

