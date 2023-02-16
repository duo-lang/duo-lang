module Parser.Terms
  ( termP
  , termCaseP) where

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
import Syntax.CST.Names
import Loc
import Parser.Types (typP)

--------------------------------------------------------------------------------------------
-- Substitutions and implicit substitutions
--------------------------------------------------------------------------------------------

termOrStarP :: Parser CST.TermOrStar
termOrStarP = starP <|> nonStarP
  where
    starP = do
      symbolP SymImplicit
      sc
      pure CST.ToSStar
    nonStarP = do
      (tm, _) <- term2P
      sc
      pure (CST.ToSTerm tm)

substitutionIP :: Parser (CST.SubstitutionI, SourcePos)
substitutionIP = do
     s <- optional $ do
      (args,_) <- parensP (termOrStarP `sepBy` (symbolP SymComma >> sc))
      pure (CST.MkSubstitutionI args)
     pos <- getSourcePos
     return (Data.Maybe.fromMaybe (CST.MkSubstitutionI []) s,pos)


--------------------------------------------------------------------------------------------
-- Free Variables and Xtors
--------------------------------------------------------------------------------------------

freeVar :: Parser (CST.Term, SourcePos)
freeVar = do
  startPos <- getSourcePos
  (v, endPos) <- freeVarNameP
  return (CST.Var (Loc startPos endPos) v, endPos)

primTermP :: Parser (CST.Term, SourcePos)
primTermP = do
  startPos <- getSourcePos
  (nm, _pos) <- primNameP
  subst <- optional $ do
    (args,_) <- parensP ( (fst <$> term3P) `sepBy` (symbolP SymComma >> sc))
    pure (CST.MkSubstitution args)
  endPos <- getSourcePos
  pure (CST.PrimTerm (Loc startPos endPos) nm (Data.Maybe.fromMaybe (CST.MkSubstitution []) subst), endPos)

xtorP :: Parser (CST.Term, SourcePos)
xtorP = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorNameP
  typ <- (fst <$>) <$> optional (bracketsP (fst <$> typP))
  (subst, _) <- substitutionIP
  afterSemi <- optional $ fst <$> do
    try (sc >> symbolP SymDoubleSemi)
    sc
    term2P
  endPos <- getSourcePos
  case afterSemi of
    Nothing -> pure (CST.Xtor (Loc startPos endPos) xt typ subst, endPos)
    Just tm -> pure (CST.Semi (Loc startPos endPos) xt subst tm, endPos)


--------------------------------------------------------------------------------------------
-- Literals and primitives
--------------------------------------------------------------------------------------------

charLitP :: Parser (CST.Term, SourcePos)
charLitP = do
  startPos <- getSourcePos
  (c, endPos) <- charP
  return (CST.PrimLitChar (Loc startPos endPos) c, endPos)

stringLitP :: Parser (CST.Term, SourcePos)
stringLitP = do
  startPos <- getSourcePos
  (c, endPos) <- stringP
  return (CST.PrimLitString (Loc startPos endPos) c, endPos)

natLitP :: CST.NominalStructural -> Parser (CST.Term, SourcePos)
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
  sc
  (v, _pos) <- freeVarNameP
  symbolP SymDot
  sc
  (cmd, endPos) <- term3P
  pure (CST.MuAbs (Loc startPos endPos) v cmd, endPos)


-------------------------------------------------------------------------------------------
-- BNF Grammar
-------------------------------------------------------------------------------------------
--
-- Square brackets [] are part of the grammar syntax and denote optional parts of a production
--
-- cse ::= pat => e
-- v   ::= x | *
--
-- t0  ::= x
--      | primcmd 
--      | n
--      | C(t3,...,t3)[{t3}] [ ;; t3]
--      | case { cse,...,cse }    
--      | case t { cse,...,cse }    
--      | cocase { cse,...,cse }    
--      | cocase t { cse,...,cse }    
--      | (t3)
--      | \x => t3
--
-- t1 ::= t0 ... t0 (n-ary application, left associative, n >= 1)
--      | t0
--
-- t2 ::= t1.D(t3,...,t3). ... .D(t3,...,t3) (n-ary destructor application, n >= 1)
--      | t1
-- 
-- t3 ::= t2 >> t2
--      | t2
--
--
-------------------------------------------------------------------------------------------
-- Pattern Parser
-------------------------------------------------------------------------------------------

-- | Parse an implicit argument pattern of the form: `*`
patStarP :: Parser CST.Pattern
patStarP = do
  startPos <- getSourcePos
  symbolP SymImplicit
  endPos <- getSourcePos
  sc
  pure (CST.PatStar (Loc startPos endPos))

-- | Parse a wildcard pattern of the form: `_`
patWildcardP :: Parser CST.Pattern
patWildcardP = do
  startPos <- getSourcePos
  symbolP SymWildcard
  endPos <- getSourcePos
  sc
  pure (CST.PatWildcard (Loc startPos endPos))

-- | Parse a variable pattern of the form: `x`
patVariableP :: Parser CST.Pattern
patVariableP = do
  startPos <- getSourcePos
  (fv, endPos) <- freeVarNameP
  sc
  pure (CST.PatVar (Loc startPos endPos) fv)

-- | Parses a list of patterns in parentheses, or nothing at all: `(pat_1,...,pat_n)`
patternListP :: Parser ([CST.Pattern], SourcePos)
patternListP = do
  s <- optional $ do
    (args,_) <- parensP (patternP `sepBy` (symbolP SymComma >> sc))
    pure args
  endPos <- getSourcePos
  return (Data.Maybe.fromMaybe [] s, endPos)

-- | Parse a xtor pattern of the form: `Xtor(pat_1,...,pat_n)` or `Xtor`
patXtorP :: Parser CST.Pattern
patXtorP = do
  startPos <- getSourcePos
  (xt, _pos) <- xtorNameP
  (args,endPos) <- patternListP
  sc
  pure (CST.PatXtor (Loc startPos endPos) xt args)



-- | Parses an arbitrary pattern
patternP :: Parser CST.Pattern
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
  (cases, endPos) <- bracesP (termCaseP `sepBy` (symbolP SymComma >> sc))
  pure (CST.Case (Loc startPos endPos) cases, endPos)

-- | Parses the second half of a "caseof" construct, i.e.
--       case tm of { termcases }
--            ^^^^^^^^^^^^^^^^^^^
caseOfRestP :: SourcePos -- ^ The source position of the start of the "case" keyword
            -> Parser (CST.Term, SourcePos)
caseOfRestP startPos =  do
  (arg, _pos) <- term2P
  _ <- keywordP KwOf
  sc
  (cases, endPos) <- bracesP (termCaseP `sepBy` (symbolP SymComma >> sc))
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
  (cases, endPos) <- bracesP (termCaseP `sepBy` (symbolP SymComma >> sc))
  return (CST.Cocase (Loc startPos endPos) cases, endPos)

-- | Parses the second half of a "caseof" construct, i.e.
--       cocase tm of { termcases }
--              ^^^^^^^^^^^^^^^^^^^
cocaseOfRestP :: SourcePos -- ^ The source position of the start of the "cocase" keyword
              -> Parser (CST.Term, SourcePos)
cocaseOfRestP startPos =  do
  (arg, _pos) <- term2P
  _ <- keywordP KwOf
  sc
  (cases, endPos) <- bracesP (termCaseP `sepBy` (symbolP SymComma >> sc))
  return (CST.CocaseOf (Loc startPos endPos) arg cases, endPos)

termCaseP :: Parser CST.TermCase
termCaseP =  do
  startPos <- getSourcePos
  pat <- patternP
  symbolP SymDoubleRightArrow
  sc
  (t, endPos) <- term3P
  pure CST.MkTermCase { CST.tmcase_loc  = Loc startPos endPos
                      , CST.tmcase_pat = pat
                      , CST.tmcase_term  = t
                      }

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
    (tm, endPos) <- term2P
    let t = foldr (CST.Lambda (Loc startPos endPos)) tm bvars
    return (t,endPos)
   )
   <|>
   (do
    symbolP SymDoubleCoRightArrow
    sc
    (tm, endPos) <- term2P
    let t = foldr (CST.CoLambda (Loc startPos endPos)) tm bvars
    return (t,endPos) )


termParensP :: Parser (CST.Term, SourcePos)
termParensP = do
  startPos <- getSourcePos
  (tm,endPos) <- parensP (fst <$> term3P)
  return (CST.TermParens (Loc startPos endPos) tm, endPos)


-- b  ::= x
--      | n
--      | C(t3,...,t3)
--      | match t with {...}
--      | comatch {...}
--      | (t3)
--      | \x => t3
term0P :: Parser (CST.Term, SourcePos)
term0P =
  termParensP <|>
  freeVar <|>
  stringLitP <|>
  charLitP <|>
  i64LitP <|>
  f64LitP <|>
  primTermP <|>
  natLitP CST.Structural <|>
  natLitP CST.Nominal <|>
  xtorP <|>
  caseP <|>
  cocaseP <|>
  muAbstraction  <|>
  lambdaP

-------------------------------------------------------------------------------------------
-- Level 1 Parser
--
-- Destructor chains.
-------------------------------------------------------------------------------------------

-- | Parses "D(t3,..*.,t3)"
destructorP :: Parser (XtorName, CST.SubstitutionI, SourcePos)
destructorP = do
  (xt, _) <- xtorNameP
  (substi, endPos) <- substitutionIP
  return (xt, substi, endPos)

term1P :: Parser (CST.Term, SourcePos)
term1P =  do
  -- Parse a termMiddleP
  startPos <- getSourcePos
  (destructee, endPos) <- term0P
  -- Parse a list of ".D(...)" applications
  destructorChain <- many (symbolP SymDot >> destructorP)
  let (res,_) = foldl (\(tm,sp) (xtor,toss,pos) -> (CST.Dtor (Loc sp pos) xtor tm toss,pos)) (destructee,startPos) destructorChain
  pure (res, endPos)

-------------------------------------------------------------------------------------------
-- Level 2 Parser
--
-- Function applications
-------------------------------------------------------------------------------------------

-- t2 ::= t1 ... t1 (n-ary application, left associative)
--      | t1
term2P :: Parser (CST.Term, SourcePos)
term2P = do
  startPos <- getSourcePos
  term <- term1P
  aterms <- many (try (scne >> term1P))
  sc
  pure (mkApps startPos (term:aterms))
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
-- Level 3 Parser
--
-- Commands
-------------------------------------------------------------------------------------------

term3P :: Parser(CST.Term, SourcePos)
term3P = do
  startPos <- getSourcePos
  d@(prd,_) <- term2P
  -- Optionally parse the rest of a command, i.e. " >> t2"
  m <- optional (symbolP SymCommand >> sc >> term2P)
  endPos <- getSourcePos
  return $ case m of
    Nothing -> d
    Just (cns, _) -> (CST.Apply (Loc startPos endPos) prd cns, endPos)

-------------------------------------------------------------------------------------------
-- Exported Parsers
-------------------------------------------------------------------------------------------

termP :: Parser CST.Term
termP = fst <$> term3P

