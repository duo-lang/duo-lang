module Parser.Terms
  ( termP
  , termCaseP) where

import Data.Foldable
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
import Syntax.Common.Names
import Syntax.Common.Primitives
import Utils

--------------------------------------------------------------------------------------------
-- Substitutions and implicit substitutions
--------------------------------------------------------------------------------------------

termOrStarP :: Parser (CST.TermOrStar, SourcePos)
termOrStarP = starP <|> nonStarP
  where
    starP = do
      symbolP SymImplicit
      pos <- getSourcePos
      sc
      pure (CST.ToSStar, pos)
    nonStarP = do
      (tm, pos) <- termTopP
      pure (CST.ToSTerm tm, pos)

substitutionIP :: Parser ([CST.TermOrStar], SourcePos)
substitutionIP = do
     s <- optional $ do
      (args,_) <- parensP ((fst <$> termOrStarP) `sepBy` (symbolP SymComma >> sc))
      pure args
     pos <- getSourcePos
     return (Data.Maybe.fromMaybe [] s,pos)


--------------------------------------------------------------------------------------------
-- Free Variables and Xtors
--------------------------------------------------------------------------------------------

freeVar :: Parser (CST.Term, SourcePos)
freeVar = do
  startPos <- getSourcePos
  (v, endPos) <- freeVarNameP
  sc
  return (CST.Var (Loc startPos endPos) v, endPos)

xtorP :: Parser (CST.Term, SourcePos)
xtorP = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorNameP
  (subst, _) <- substitutionIP
  sc
  afterSemi <- optional $ fst <$> do
    symbolP SymDoubleSemi
    sc
    termTopP
  endPos <- getSourcePos
  case afterSemi of
    Nothing -> pure (CST.Xtor (Loc startPos endPos) xt subst, endPos)
    Just tm -> pure (CST.Semi (Loc startPos endPos) xt subst tm, endPos)


--------------------------------------------------------------------------------------------
-- Literals and primitives
--------------------------------------------------------------------------------------------

charLitP :: Parser (CST.Term, SourcePos)
charLitP = do
  startPos <- getSourcePos
  (c, endPos) <- charP
  sc
  return (CST.PrimLitChar (Loc startPos endPos) c, endPos)

stringLitP :: Parser (CST.Term, SourcePos)
stringLitP = do
  startPos <- getSourcePos
  (c, endPos) <- stringP
  sc
  return (CST.PrimLitString (Loc startPos endPos) c, endPos)

natLitP :: CST.NominalStructural -> Parser (CST.Term, SourcePos)
natLitP ns = do
  startPos <- getSourcePos
  () <- checkTick ns
  (num, endPos) <- natP <* notFollowedBy (symbolP SymHash)
  sc
  return (CST.NatLit (Loc startPos endPos) ns num, endPos)

f64LitP :: Parser (CST.Term, SourcePos)
f64LitP = do
  startPos <- getSourcePos
  (double, endPos) <- try $ do
    (double,_) <- floatP
    endPos <- keywordP KwF64
    sc
    pure (double, endPos)
  pure (CST.PrimLitF64 (Loc startPos endPos) double, endPos)

i64LitP :: Parser (CST.Term, SourcePos)
i64LitP = do
  startPos <- getSourcePos
  (int, endPos) <- try $ do
    (int,_) <- intP
    endPos <- keywordP KwI64
    sc
    pure (int, endPos)
  pure (CST.PrimLitI64 (Loc startPos endPos) int, endPos)

--------------------------------------------------------------------------------------------
-- Mu abstractions
--------------------------------------------------------------------------------------------

muAbstraction :: Parser (CST.Term, SourcePos)
muAbstraction =  do
  startPos <- getSourcePos
  _ <- keywordP KwMu
  sc
  (v, _pos) <- freeVarNameP
  symbolP SymDot
  sc
  (cmd, endPos) <- termTopP
  pure (CST.MuAbs (Loc startPos endPos) v cmd, endPos)


--------------------------------------------------------------------------------------------
-- Commands
--------------------------------------------------------------------------------------------

exitSuccessCmdP :: Parser (CST.Term, SourcePos)
exitSuccessCmdP = do
  startPos <- getSourcePos
  endPos <- keywordP KwExitSuccess
  sc
  return (CST.PrimCmdTerm $ CST.ExitSuccess (Loc startPos endPos), endPos)

exitFailureCmdP :: Parser (CST.Term, SourcePos)
exitFailureCmdP = do
  startPos <- getSourcePos
  endPos <- keywordP KwExitFailure
  sc
  return (CST.PrimCmdTerm $ CST.ExitFailure (Loc startPos endPos), endPos)

printCmdP :: Parser (CST.Term, SourcePos)
printCmdP = do
  startPos <- getSourcePos
  _ <- keywordP KwPrint
  (arg,_) <- parensP (fst <$> termTopP)
  sc
  symbolP SymSemi
  sc
  (cmd, endPos) <- termTopP
  return (CST.PrimCmdTerm $ CST.Print (Loc startPos endPos) arg cmd, endPos)

readCmdP :: Parser (CST.Term, SourcePos)
readCmdP = do
  startPos <- getSourcePos
  _ <- keywordP KwRead
  (arg,endPos) <- bracketsP (fst <$> termTopP)
  sc
  return (CST.PrimCmdTerm $ CST.Read (Loc startPos endPos) arg, endPos)

primitiveCmdP :: Parser (CST.Term, SourcePos)
primitiveCmdP = do
  startPos <- getSourcePos
  (pt, op, _) <- asum (uncurry primOpKeywordP <$> keys primOps)
  (subst,endPos) <- parensP ( (fst <$> termTopP) `sepBy` (symbolP SymComma >> sc))
  sc
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
-- cse ::= pat => e
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
-- Pattern Parser
-------------------------------------------------------------------------------------------

-- | Parse an implicit argument pattern of the form: `*`
patStarP :: Parser (CST.Pattern, SourcePos)
patStarP = do
  startPos <- getSourcePos
  symbolP SymImplicit
  endPos <- getSourcePos
  sc
  pure (CST.PatStar (Loc startPos endPos), endPos)

-- | Parse a wildcard pattern of the form: `_`
patWildcardP :: Parser (CST.Pattern, SourcePos)
patWildcardP = do
  startPos <- getSourcePos
  symbolP SymWildcard
  endPos <- getSourcePos
  sc
  pure (CST.PatWildcard (Loc startPos endPos), endPos)

-- | Parse a variable pattern of the form: `x`
patVariableP :: Parser (CST.Pattern, SourcePos)
patVariableP = do
  startPos <- getSourcePos
  (fv, endPos) <- freeVarNameP
  sc
  pure (CST.PatVar (Loc startPos endPos) fv, endPos)

-- | Parses a list of patterns in parentheses, or nothing at all: `(pat_1,...,pat_n)`
patternListP :: Parser ([CST.Pattern], SourcePos)
patternListP = do
  s <- optional $ do
    (args,_) <- parensP ((fst <$> patternP) `sepBy` (symbolP SymComma >> sc))
    pure args
  endPos <- getSourcePos
  return (Data.Maybe.fromMaybe [] s, endPos)

-- | Parse a xtor pattern of the form: `Xtor(pat_1,...,pat_n)` or `Xtor`
patXtorP :: Parser (CST.Pattern, SourcePos)
patXtorP = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorNameP
  (args,endPos) <- patternListP
  sc
  pure (CST.PatXtor (Loc startPos endPos) xt args, endPos)



-- | Parses an arbitrary pattern
patternP :: Parser (CST.Pattern, SourcePos)
patternP =
  patStarP <|>
  patWildcardP <|>
  patXtorP <|>
  patVariableP


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
  sc
  caseRestP startPos <|> caseOfRestP startPos

-- | Parses the second half of a "case" construct, i.e.
--       case { termcases }
--            ^^^^^^^^^^^^^
caseRestP :: SourcePos -- ^ The source position of the start of the "case" keyword
          -> Parser (CST.Term, SourcePos)
caseRestP startPos = do
  (cases, endPos) <- bracesP ((fst <$> termCaseP) `sepBy` (symbolP SymComma >> sc))
  sc
  pure (CST.Case (Loc startPos endPos) cases, endPos)

-- | Parses the second half of a "caseof" construct, i.e.
--       case tm of { termcases }
--            ^^^^^^^^^^^^^^^^^^^
caseOfRestP :: SourcePos -- ^ The source position of the start of the "case" keyword
            -> Parser (CST.Term, SourcePos)
caseOfRestP startPos =  do
  (arg, _pos) <- termTopP
  _ <- keywordP KwOf
  sc
  (cases, endPos) <- bracesP ((fst <$> termCaseP) `sepBy` (symbolP SymComma >> sc))
  sc
  return (CST.CaseOf (Loc startPos endPos) arg cases, endPos)

-- | Parses all constructs of the forms:
--       cocase { termcases }
--       cocase tm of { termcases }
cocaseP :: Parser (CST.Term, SourcePos)
cocaseP = do
  startPos <- getSourcePos
  _ <- keywordP KwCocase
  sc
  cocaseRestP startPos <|> cocaseOfRestP startPos

-- | Parses the second half of a "cocase" construct, i.e.
--       cocase { termcases }
--              ^^^^^^^^^^^^^
cocaseRestP :: SourcePos -- ^ The source position of the start of the "cocase" keyword
            -> Parser (CST.Term, SourcePos)
cocaseRestP startPos = do
  (cases, endPos) <- bracesP ((fst <$> termCaseP) `sepBy` (symbolP SymComma >> sc))
  sc
  return (CST.Cocase (Loc startPos endPos) cases, endPos)

-- | Parses the second half of a "caseof" construct, i.e.
--       cocase tm of { termcases }
--              ^^^^^^^^^^^^^^^^^^^
cocaseOfRestP :: SourcePos -- ^ The source position of the start of the "cocase" keyword
              -> Parser (CST.Term, SourcePos)
cocaseOfRestP startPos =  do
  (arg, _pos) <- termTopP
  _ <- keywordP KwOf
  sc
  (cases, endPos) <- bracesP ((fst <$> termCaseP) `sepBy` (symbolP SymComma >> sc))
  sc
  return (CST.CocaseOf (Loc startPos endPos) arg cases, endPos)

termCaseP :: Parser (CST.TermCase, SourcePos)
termCaseP =  do
  startPos <- getSourcePos
  (pat,_) <- patternP
  symbolP SymDoubleRightArrow
  sc
  (t, endPos) <- termTopP
  let pmcase = CST.MkTermCase { tmcase_loc  = Loc startPos endPos
                              , tmcase_pat = pat
                              , tmcase_term  = t }
  return (pmcase, endPos)

--------------------------------------------------------------------------------------------
-- CST-Sugar
--------------------------------------------------------------------------------------------

lambdaP :: Parser (CST.Term, SourcePos)
lambdaP = do
  startPos <- getSourcePos
  symbolP SymBackslash
  bvars <- some $ fst <$> (freeVarNameP <* sc)
  (do
    symbolP SymDoubleRightArrow
    sc
    (tm, endPos) <- termTopP
    let t = foldr (CST.Lambda (Loc startPos endPos)) tm bvars
    return (t,endPos)
   )
   <|>
   (do
    symbolP SymDoubleCoRightArrow
    sc
    (tm, endPos) <- termTopP
    let t = foldr (CST.CoLambda (Loc startPos endPos)) tm bvars
    return (t,endPos) )


termParensP :: Parser (CST.Term, SourcePos)
termParensP = do
  startPos <- getSourcePos
  (tm,endPos) <- parensP (fst <$> termTopP)
  sc
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
  stringLitP <|>
  charLitP <|>
  i64LitP <|>
  f64LitP <|>
  primitiveCmdP <|>
  natLitP CST.Structural <|>
  natLitP CST.Nominal <|>
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
--
-- Function applications
-------------------------------------------------------------------------------------------

-- m ::= b ... b (n-ary application, left associative)
--     | b
termMiddleP :: Parser (CST.Term, SourcePos)
termMiddleP = do
  startPos <- getSourcePos
  aterms <- some termBotP
  pure (mkApps startPos aterms)
  where
    mkApps :: SourcePos -> [(CST.Term, SourcePos)] -> (CST.Term, SourcePos)
    mkApps _startPos []  = error "Impossible! The `some` parser in applicationP parses at least one element."
    mkApps _startPos [x] = x
    mkApps startPos ((a1,_):(a2,endPos):as) =
      let
        tm = CST.FunApp (Loc startPos endPos) a1 a2
      in
        mkApps startPos ((tm,endPos):as)

-------------------------------------------------------------------------------------------
-- Top Parser
--
-- Destructor chains.
-------------------------------------------------------------------------------------------

-- | Parses "D(t,..*.,t)"
destructorP :: Parser (XtorName, [CST.TermOrStar], SourcePos)
destructorP = do
  (xt, _) <- xtorNameP
  (substi, endPos) <- substitutionIP
  sc
  return (xt, substi, endPos)

termTopP :: Parser (CST.Term, SourcePos)
termTopP =  do
  -- Parse a termMiddleP
  startPos <- getSourcePos
  (destructee, endPos) <- termMiddleP
  -- Parse a list of ".D(...)" applications
  destructorChain <- many (symbolP SymDot >> destructorP)
  let (res,_) = foldl (\(tm,sp) (xtor,toss,pos) -> (CST.Dtor (Loc sp pos) xtor tm toss,pos)) (destructee,startPos) destructorChain
  let d = (res, endPos)
  -- Optionally parse the rest of a command, i.e. " >> t"
  m <- optional (symbolP SymCommand >> sc >> termTopP)
  endPos <- getSourcePos
  return $ case m of
    Nothing -> d
    Just x -> (CST.Apply (Loc startPos endPos) (fst d) (fst x), endPos)

-------------------------------------------------------------------------------------------
-- Exported Parsers
-------------------------------------------------------------------------------------------

termP :: Parser (CST.Term, SourcePos)
termP = termTopP

