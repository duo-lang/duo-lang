module Parser.Terms
  ( termP)where

import Data.Bifunctor (first)
import Data.Foldable
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (keys)
import Data.Maybe qualified
import Text.Megaparsec
    ( SourcePos,
      optional,
      (<|>),
      getSourcePos,
      many,
      sepBy,
      some,
      MonadParsec(try, notFollowedBy) )
import Parser.Common
import Parser.Definition
import Parser.Lexer
import Syntax.CST.Terms qualified as CST
import Syntax.Common
import Utils

--------------------------------------------------------------------------------------------
-- Substitutions and implicit substitutions
--------------------------------------------------------------------------------------------

-- | Parse a substitution,
-- E.g.: "(t1,t2,t3)"
substitutionP :: Parser ([CST.Term], SourcePos)
substitutionP = do
     s <- optional $ fst <$> parens ( (fst <$> termTopP) `sepBy` symbolP SymComma)
     pos <- getSourcePos
     return (Data.Maybe.fromMaybe [] s,pos)

termOrStarP :: Parser (CST.TermOrStar, SourcePos)
termOrStarP = ((\s -> (CST.ToSStar,s)) <$> symbolP SymImplicit) <|> (first CST.ToSTerm <$> termTopP)


substitutionIP :: Parser ([CST.TermOrStar], SourcePos)
substitutionIP = do
     s <- optional $ fst <$> parens  ((fst <$> termOrStarP) `sepBy` symbolP SymComma)
     pos <- getSourcePos
     return (Data.Maybe.fromMaybe [] s,pos)


--------------------------------------------------------------------------------------------
-- Binding sites and implicit binding sites
--------------------------------------------------------------------------------------------

bindingP :: Parser (CST.FVOrStar , SourcePos)
bindingP =  (do _ <- symbolP SymImplicit ;  pos <- getSourcePos; return (CST.FoSStar ,pos))  <|> (first CST.FoSFV <$> freeVarNameP)


bindingSiteP :: Parser (CST.BindingSite, SourcePos)
bindingSiteP = do
  s <- optional $ fst <$> (parens ((fst <$> bindingP) `sepBy` symbolP SymComma))
  endPos <- getSourcePos
  return (Data.Maybe.fromMaybe [] s, endPos)

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
    _ <- symbolP SymDoubleSemi
    termTopP
  endPos <- getSourcePos
  case afterSemi of
    Nothing -> pure (CST.Xtor (Loc startPos endPos) xt subst, endPos)
    Just _tm -> undefined -- pure (CST.Semi (Loc startPos endPos) xt subst tm, endPos)


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
muAbstraction =  do
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
applyCmdP =  do
  --startPos <- getSourcePos
  _ <- symbolP SymCommand
  (cns, endPos) <- termTopP
  return (cns,endPos)

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
-- t ::= m.D(t,...,t). ... .D(t,...,t) [ >> m] (n-ary destructor application, n >= 1, also commands)
--     | m
-- 



-------------------------------------------------------------------------------------------
-- Bottom Parser
-------------------------------------------------------------------------------------------

-- | Parses all constructs of the forms:
--       case { termcases }
--       case tm of { termcases }
caseP :: Parser (CST.Term, SourcePos)
caseP = do
  startPos <- getSourcePos
  _ <- keywordP KwCase
  caseRestP startPos <|> caseOfRestP startPos

-- | Parses the second half of a "case" construct, i.e.
--       case { termcases }
--            ^^^^^^^^^^^^^
caseRestP :: SourcePos -- ^ The source position of the start of the "case" keyword
          -> Parser (CST.Term, SourcePos)
caseRestP startPos = do
  (cases, endPos) <- braces ((fst <$> termCaseP) `sepBy` symbolP SymComma)
  pure (CST.Case (Loc startPos endPos) cases, endPos)

-- | Parses the second half of a "caseof" construct, i.e.
--       case tm of { termcases }
--            ^^^^^^^^^^^^^^^^^^^
caseOfRestP :: SourcePos -- ^ The source position of the start of the "case" keyword
            -> Parser (CST.Term, SourcePos)
caseOfRestP startPos =  do
  (arg, _pos) <- termTopP
  _ <- keywordP KwOf
  (cases, endPos) <- braces ((fst <$> termCaseP) `sepBy` symbolP SymComma)
  return (CST.CaseOf (Loc startPos endPos) arg cases, endPos)

-- | Parses all constructs of the forms:
--       cocase { termcases }
--       cocase tm of { termcases }
cocaseP :: Parser (CST.Term, SourcePos)
cocaseP = do
  startPos <- getSourcePos
  _ <- keywordP KwCocase
  cocaseRestP startPos <|> cocaseOfRestP startPos

-- | Parses the second half of a "cocase" construct, i.e.
--       cocase { termcases }
--              ^^^^^^^^^^^^^
cocaseRestP :: SourcePos -- ^ The source position of the start of the "cocase" keyword
            -> Parser (CST.Term, SourcePos)
cocaseRestP startPos = do
  (cases, endPos) <- braces ((fst <$> termCaseP) `sepBy` symbolP SymComma)
  return (CST.Cocase (Loc startPos endPos) cases, endPos)

-- | Parses the second half of a "caseof" construct, i.e.
--       cocase tm of { termcases }
--              ^^^^^^^^^^^^^^^^^^^
cocaseOfRestP :: SourcePos -- ^ The source position of the start of the "cocase" keyword
              -> Parser (CST.Term, SourcePos)
cocaseOfRestP startPos =  do
  (arg, _pos) <- termTopP
  _ <- keywordP KwOf
  (cases, endPos) <- braces ((fst <$> termCaseP) `sepBy` symbolP SymComma)
  return (CST.CocaseOf (Loc startPos endPos) arg cases, endPos)

termCaseP :: Parser (CST.TermCase, SourcePos)
termCaseP =  do
  startPos <- getSourcePos
  (xt, _pos) <- xtorNameP
  (args,_) <- bindingSiteP
  _ <- symbolP SymDoubleRightArrow
  (t, endPos) <- termTopP
  let pmcase = CST.MkTermCase { tmcase_loc  = Loc startPos endPos
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
termBotP = freeVar <|>
  i64LitP <|>
  f64LitP <|>
  primitiveCmdP <|>
  natLitP Structural <|>
  natLitP Nominal <|>
  xtorP <|>
  caseP <|>
  cocaseP <|>
  muAbstraction  <|>
  termParensP <|>
  lambdaP <|>
  readCmdP <|>
  printCmdP <|>
  exitFailureCmdP <|>
  exitSuccessCmdP


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
termMiddleP =  applicationP -- applicationP handles the case of 0-ary application

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
dtorP =  do
  startPos <- getSourcePos
  (destructee, endPos) <- termMiddleP
  destructorChain <- destructorChainP
  case destructorChain of
    [] -> return (destructee, endPos)
    (x:xs) -> return (CST.DtorChain startPos destructee (x :| xs), endPos)

termTopP :: Parser (CST.Term, SourcePos)
termTopP =  do
  startPos <- getSourcePos
  d <- dtorP
  m <- optional $ applyCmdP
  endPos <- getSourcePos
  return $ case m of
    Nothing -> d
    Just x -> (CST.Apply (Loc startPos endPos) (fst d) (fst x), endPos)



-------------------------------------------------------------------------------------------
-- Exported Parsers
-------------------------------------------------------------------------------------------

termP :: Parser (CST.Term, SourcePos)
termP = termTopP

