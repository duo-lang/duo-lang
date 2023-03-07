module Syntax.RST.Terms
  ( -- Terms
    Term(..)
  , PrdCnsTerm(..)
  , Substitution(..)
  , SubstitutionI(..)
  , GenericPattern
  , PatternNew(..)
  , StarPattern(..)
  , Pattern(..)
  , PatternI(..)
  , TermCase(..)
  , TermCaseI(..)
  , CmdCase(..)
  , InstanceCase(..)
  , Command(..)
  , PrimitiveOp(..)
  , Overlap 
   -- Functions
  ,overlap) where

import Data.List (elemIndex, tails)
import Data.Text (Text, pack)

import Loc ( Loc, HasLoc(..) )
import Syntax.CST.Names
    ( ClassName, FreeVarName, MethodName, XtorName, unFreeVarName, unXtorName )
import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types ( PrdCnsRep(..), PrdCns(..) )
import Syntax.LocallyNameless (LocallyNameless (..), Index)
import Syntax.NMap (NMap (..), (<¢>))
import Syntax.RST.Types ( Typ, Polarity(..) )

---------------------------------------------------------------------------------
-- Variable representation
--
-- We use the locally nameless representation for terms, which combines names for
-- free variables with  anonymous deBruijn indexes for bound variables.
-- The locally namelesss representation is well documented here:
-- https://www.chargueraud.org/softs/ln/
---------------------------------------------------------------------------------

---------------------------------------------------------------------------------
-- Substitutions and Substitutions with implicit argument.
--
-- A substitution is a list of producer and consumer terms.
---------------------------------------------------------------------------------

data PrdCnsTerm where
  PrdTerm :: Term Prd -> PrdCnsTerm
  CnsTerm :: Term Cns -> PrdCnsTerm

deriving instance Show PrdCnsTerm

newtype Substitution =
  MkSubstitution { unSubstitution :: [PrdCnsTerm] }

deriving instance Show Substitution

instance NMap Substitution PrdCnsTerm where
  nmap f = MkSubstitution . fmap f . (\x -> x.unSubstitution)
  nmapM f = fmap MkSubstitution . mapM f . (\x -> x.unSubstitution)

-- | A SubstitutionI is like a substitution where one of the arguments has been
-- replaced by an implicit argument. The following convention for the use of the
-- `pc` parameter is used:
--
-- SubstitutionI Prd = ... [*] ...
-- SubstitutionI Cns = ... (*) ...
newtype SubstitutionI (pc :: PrdCns) =
  MkSubstitutionI { unSubstitutionI :: ([PrdCnsTerm], PrdCnsRep pc, [PrdCnsTerm]) }

deriving instance Show (SubstitutionI pc)

---------------------------------------------------------------------------------
-- Pattern/copattern match cases
---------------------------------------------------------------------------------

type GenericPattern = Either PatternNew StarPattern

data PatternNew where
  PatXtor     :: Loc -> PrdCns -> CST.NominalStructural -> XtorName -> [PatternNew] -> PatternNew
  PatVar      :: Loc -> PrdCns -> FreeVarName -> PatternNew
  PatWildcard :: Loc -> PrdCns -> PatternNew

--------------------------------------------

type OverlapMsg = Text

type Overlap = Maybe OverlapMsg

-- | Generates the Overlap of Patterns between one another.
-- For testing purposes, best display via printOverlap $ overlap test<X>...
overlap :: [GenericPattern] -> Overlap
overlap l = let pairOverlaps = concat $ zipWith map (map (overlapA2) l) (tail (tails l))
            in  concatOverlaps pairOverlaps
  where
    -- | Reduces multiple potential Overlap Messages into one potential Overlap Message.
    concatOverlaps :: [Overlap] -> Overlap
    concatOverlaps xs =
      let concatRule = \x y -> x <> "\n\n" <> y
      in  foldr (liftm2 concatRule) Nothing xs
      where
        liftm2 :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a
        liftm2 _ x          Nothing   = x
        liftm2 _ Nothing    y         = y
        liftm2 f (Just x)   (Just y)  = Just $ (f x y)

    -- | Generates an Overlap Message for patterns p1 p2.
    overlapMsg :: GenericPattern -> GenericPattern -> OverlapMsg
    overlapMsg p1 p2 =
      let p1Str = patternToText p1
          p2Str = patternToText p2
      in  "Overlap found:\n" <> p1Str <> " overlaps with " <> p2Str <> "\n"

    -- | Readable Conversion of Pattern to Text.
    patternToText :: GenericPattern -> Text
    patternToText (Left  (PatVar       loc prdcns varName))      = pack(show prdcns) <> pack(" Variable Pattern ") <> pack("'") <> varName.unFreeVarName <> pack("'") <> pack(" in: " ++ (show loc))
    patternToText (Left  (PatWildcard  loc prdcns))              = pack(show prdcns) <> pack(" Wildcard Pattern in: ") <> pack(show loc)
    patternToText (Left  (PatXtor      loc prdcns _ xtorName _)) = pack(show prdcns) <> pack(" Xtor Pattern ") <> pack("'") <> xtorName.unXtorName <> pack("'") <> pack(" in: " ++ (show loc))
    patternToText (Right (PatXtorStar  loc prdcns _ xtorName _)) = pack(show prdcns) <> pack(" Xtor Pattern ") <> pack("'") <> xtorName.unXtorName <> pack("'") <> pack(" in: " ++ (show loc))
    patternToText (Right (PatStar      loc prdcns))              = pack(show prdcns) <> pack(" Star Pattern in: ") <> pack(show loc)

    -- | Determines for 2x Patterns p1 p2 a potential Overlap message on p1 'containing' p2 or p2 'containing' p1.
    overlapA2 :: GenericPattern -> GenericPattern -> Overlap
    -- Basic Idea:  Only if both ARE De/Constructors, overlap occurs when their names match and all subpatterns overlap pairwise.
    --              If one or both of p1,p2 are NOT a De/Constructor we always already have overlap (last case as catchall).
    -- Xtor Cases: In our current Pattern Syntax, a Xtor Pattern can be constructed as either a Base Pattern or Star Pattern,
    --             meaning that 4 match cases are needed for covering all overlapA2 Xtor Pattern cases.
      -- Case 1: 2x Base De/Constructors
    overlapA2 p1@(Left (PatXtor _ _ _ xXtorName xBasePatterns)) 
              p2@(Left (PatXtor _ _ _ yXtorName yBasePatterns)) =
                if    (xXtorName /= yXtorName)
                then  Nothing
                else  let xPatterns = map Left xBasePatterns
                          yPatterns = map Left yBasePatterns
                      in  overlapSubpatterns (p1,xPatterns) (p2,yPatterns)
      -- Case 2: Base De/Constructor and Star De/Constructor
    overlapA2 p1@(Left  (PatXtor      _ _ _ xXtorName xBasePatterns))
              p2@(Right (PatXtorStar  _ _ _ yXtorName (y1BasePatterns, star, y2BasePatterns))) =
                if    (xXtorName /= yXtorName)
                then  Nothing
                else  let xPatterns = map Left xBasePatterns
                          yPatterns = (map Left y1BasePatterns) ++ ((Right star):(map Left y2BasePatterns))
                      in  overlapSubpatterns (p1,xPatterns) (p2,yPatterns)
      -- Case 3: Star De/Constructor and Base De/Constructor -> Reduce to Case 2!
    overlapA2 p1@(Right (PatXtorStar _ _ _ _ _)) p2@(Left (PatXtor _ _ _ _ _)) = overlapA2 p2 p1
      -- Case 4: 2x Star De/Constructors
    overlapA2 p1@(Right (PatXtorStar  _ _ _ xXtorName (x1BasePatterns, xstar, x2BasePatterns)))
              p2@(Right (PatXtorStar  _ _ _ yXtorName (y1BasePatterns, ystar, y2BasePatterns))) = 
                if    (xXtorName /= yXtorName)
                then  Nothing
                else  let xPatterns = (map Left x1BasePatterns) ++ ((Right xstar):(map Left x2BasePatterns))
                          yPatterns = (map Left y1BasePatterns) ++ ((Right ystar):(map Left y2BasePatterns))
                      in  overlapSubpatterns (p1,xPatterns) (p2,yPatterns)
    -- All other cases: One of both Patterns is NOT a Xtor Pattern, therefore overlap occures!
    overlapA2 p1 p2 = Just $ overlapMsg p1 p2

    -- | For 2 Patterns with their Subpatterns, returns Overlap Message if all Pairs of Subatterns overlap,
    -- | and returns Nothing if at least one Pair of Subpatterns does not overlap 
    overlapSubpatterns ::  (GenericPattern, [GenericPattern]) -> (GenericPattern, [GenericPattern]) -> Overlap
    overlapSubpatterns (p1,xPatterns) (p2,yPatterns) = 
      let subPatternsOverlaps = zipWith overlapA2 xPatterns yPatterns
          --Only if all Pairs of Subpatterns truly overlap is an Overlap found.
          subPatternsOverlap =  if   (elem Nothing subPatternsOverlaps) 
                                then Nothing 
                                else concatOverlaps subPatternsOverlaps
      in  case subPatternsOverlap of
            Nothing                       -> Nothing
            (Just subPatternsOverlapMsg)  ->
              Just $
                (overlapMsg p1 p2)
                <> "due to the all Subpatterns overlapping as follows:\n"
                <> "--------------------------------->\n"
                <> subPatternsOverlapMsg
                <> "---------------------------------<\n"

--------------------------------------------

deriving instance Eq PatternNew
deriving instance Show PatternNew

instance HasLoc PatternNew where
  getLoc :: PatternNew -> Loc
  getLoc (PatXtor loc _ _ _ _) = loc
  getLoc (PatVar loc _ _) = loc
  getLoc (PatWildcard loc _) = loc

data StarPattern where
  PatStar     :: Loc -> PrdCns -> StarPattern
  PatXtorStar :: Loc -> PrdCns -> CST.NominalStructural -> XtorName -> ([PatternNew],StarPattern,[PatternNew]) -> StarPattern

deriving instance Eq StarPattern
deriving instance Show StarPattern

instance HasLoc StarPattern where
  getLoc :: StarPattern -> Loc
  getLoc (PatStar loc _) = loc
  getLoc (PatXtorStar loc _ _ _ _) = loc

data Pattern where
  XtorPat :: Loc -> XtorName -> [(PrdCns, Maybe FreeVarName)] -> Pattern

deriving instance Eq Pattern
deriving instance Show Pattern

data PatternI where
  XtorPatI :: Loc -> XtorName -> ([(PrdCns, Maybe FreeVarName)], (), [(PrdCns, Maybe FreeVarName)]) -> PatternI
deriving instance Eq PatternI
deriving instance Show PatternI

-- | Represents one case in a pattern match or copattern match.
--
--        X(x_1,...,x_n) => e
--        ^ ^^^^^^^^^^^     ^
--        |      |          |
--        |  tmcase_args  tmcase_term
--        |
--    tmcase_name
--
data TermCase (pc :: PrdCns)= MkTermCase
  { tmcase_loc  :: Loc
  , tmcase_pat  :: Pattern
  , tmcase_term :: Term pc
  }

deriving instance Show (TermCase pc)

-- | Represents one case in a pattern match or copattern match.
-- Does bind an implicit argument (in contrast to TermCase).
--
--        X(x_1, * ,x_n) => e
--        ^ ^^^^^^^^^^^     ^
--        |      |          |
--        |  tmcasei_args  tmcasei_term
--        |
--    tmcasei_name
--
data TermCaseI (pc :: PrdCns) = MkTermCaseI
  { tmcasei_loc  :: Loc
  , tmcasei_pat  :: PatternI
  , tmcasei_term :: Term pc
  }

deriving instance Show (TermCaseI pc)

-- | Represents one case in a pattern match or copattern match.
--
--        X Gamma           => c
--        ^ ^^^^^-----         ^------
--        |          |               |
--    cmdcase_name  cmdcase_args      cmdcase_cmd
--
data CmdCase = MkCmdCase
  { cmdcase_loc  :: Loc
  , cmdcase_pat :: Pattern
  , cmdcase_cmd  :: Command
  }

deriving instance Show CmdCase


data InstanceCase = MkInstanceCase
  { instancecase_loc :: Loc
  , instancecase_pat :: Pattern
  , instancecase_cmd :: Command
  }

deriving instance Show InstanceCase



---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

-- | A symmetric term.
data Term (pc :: PrdCns) where
   ---------------------------------------------------------------------------------
  -- Core constructs
  ---------------------------------------------------------------------------------
  -- | A bound variable in the locally nameless system.
  BoundVar :: Loc -> PrdCnsRep pc -> Index -> Term pc
  -- | A free variable in the locally nameless system.
  FreeVar :: Loc -> PrdCnsRep pc -> FreeVarName -> Term pc
  -- | A constructor or destructor.
  -- If the first argument is `PrdRep` it is a constructor, a destructor otherwise.
  Xtor :: Loc -> PrdCnsRep pc -> CST.NominalStructural -> XtorName -> Substitution -> Term pc
  -- | A pattern or copattern match.
  -- If the first argument is `PrdRep` it is a copattern match, a pattern match otherwise.
  XCase :: Loc -> PrdCnsRep pc -> CST.NominalStructural -> [CmdCase] -> Term pc
  -- | A Mu or TildeMu abstraction:
  --
  --  mu k.c    =   MuAbs PrdRep c
  -- ~mu x.c    =   MuAbs CnsRep c
  MuAbs :: Loc -> PrdCnsRep pc -> Maybe FreeVarName -> Command -> Term pc
  ---------------------------------------------------------------------------------
  -- Syntactic sugar
  ---------------------------------------------------------------------------------
  -- The two dual constructs "Dtor" and "Semi"
  --
  -- Dtor:
  --  prd.Dtor(args)
  -- Semi:
  --  C(args).cns
  Semi :: Loc -> PrdCnsRep pc -> CST.NominalStructural -> XtorName -> SubstitutionI pc -> Term Cns -> Term pc
  Dtor :: Loc -> PrdCnsRep pc -> CST.NominalStructural -> XtorName -> Term Prd -> SubstitutionI pc -> Term pc
  -- The two dual constructs "CaseOf" and "CocaseOf"
  --
  -- case   prd of { X(xs) => prd }
  -- case   prd of { X(xs) => cns }
  -- cocase cns of { X(xs) => prd }
  -- cocase cns of { X(xs) => cns }
  CaseOf   :: Loc -> PrdCnsRep pc -> CST.NominalStructural -> Term Prd -> [TermCase pc] -> Term pc
  CocaseOf :: Loc -> PrdCnsRep pc -> CST.NominalStructural -> Term Cns -> [TermCase pc] -> Term pc
  -- The two dual constructs "CaseI" and "CocaseI"
  --
  -- case   { X(xs,*,ys) => prd}
  -- case   { X(xs,*,ys) => cns}
  -- cocase { X(xs,*,ys) => prd}
  -- cocase { X(xs,*,ys) => cns}
  CaseI   :: Loc -> PrdCnsRep pc -> CST.NominalStructural -> [TermCaseI pc] -> Term Cns
  CocaseI :: Loc -> PrdCnsRep pc -> CST.NominalStructural -> [TermCaseI pc] -> Term Prd
  
  -- \x y z -> t 
  Lambda  :: Loc  -> PrdCnsRep pc -> FreeVarName -> Term pc  -> Term pc 
  
  ---------------------------------------------------------------------------------
  -- Primitive constructs
  ---------------------------------------------------------------------------------
  PrimLitI64 :: Loc -> Integer -> Term Prd
  PrimLitF64 :: Loc -> Double -> Term Prd
  PrimLitChar :: Loc -> Char -> Term Prd
  PrimLitString :: Loc -> String -> Term Prd

deriving instance Show (Term pc)


---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

data PrimitiveOp where
  -- I64 Ops
  I64Add :: PrimitiveOp
  I64Sub :: PrimitiveOp
  I64Mul :: PrimitiveOp
  I64Div :: PrimitiveOp
  I64Mod :: PrimitiveOp
  -- F64 Ops
  F64Add :: PrimitiveOp
  F64Sub :: PrimitiveOp
  F64Mul :: PrimitiveOp
  F64Div :: PrimitiveOp
  -- Char Ops
  CharPrepend :: PrimitiveOp
  -- String Ops
  StringAppend :: PrimitiveOp
  deriving (Show, Eq, Ord, Enum, Bounded)

-- | An executable command.
data Command where
  -- | A producer applied to a consumer:
  --
  --   p >> c
  Apply  :: Loc -> Term Prd -> Term Cns -> Command
  Print  :: Loc -> Term Prd -> Command -> Command
  Read   :: Loc -> Term Cns -> Command
  Jump   :: Loc -> FreeVarName -> Command
  Method :: Loc -> MethodName -> ClassName -> Maybe (Typ Pos, Typ Neg) -> Substitution -> Command
  ExitSuccess :: Loc -> Command
  ExitFailure :: Loc -> Command
  PrimOp :: Loc -> PrimitiveOp -> Substitution -> Command
  CaseOfCmd :: Loc -> CST.NominalStructural -> Term Prd -> [CmdCase] -> Command
  CaseOfI :: Loc -> PrdCnsRep pc -> CST.NominalStructural -> Term Prd -> [TermCaseI pc] -> Command
  CocaseOfCmd :: Loc -> CST.NominalStructural -> Term Cns -> [CmdCase] -> Command
  CocaseOfI :: Loc -> PrdCnsRep pc -> CST.NominalStructural -> Term Cns -> [TermCaseI pc] -> Command

deriving instance Show Command

---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

pctermOpeningRec :: Int -> Substitution -> PrdCnsTerm -> PrdCnsTerm
pctermOpeningRec k subst (PrdTerm tm) = PrdTerm $ termOpeningRec k subst tm
pctermOpeningRec k subst (CnsTerm tm) = CnsTerm $ termOpeningRec k subst tm

termOpeningRec :: Int -> Substitution -> Term pc -> Term pc
-- Core constructs
termOpeningRec k subst bv@(BoundVar _ pcrep (i,j)) | i == k    = case (pcrep, subst.unSubstitution !! j) of
                                                                      (PrdRep, PrdTerm tm) -> tm
                                                                      (CnsRep, CnsTerm tm) -> tm
                                                                      t                    -> error $ "termOpeningRec BOOM: " ++ show t
                                                   | otherwise = bv
termOpeningRec _ _ fv@FreeVar {}= fv
termOpeningRec k args (Xtor loc rep ns xt subst) =
  Xtor loc rep ns xt (pctermOpeningRec k args <¢> subst)
termOpeningRec k args (XCase loc rep ns cases) =
  XCase loc rep ns $ map (\pmcase -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args pmcase.cmdcase_cmd }) cases
termOpeningRec k args (MuAbs loc rep fv cmd) =
  MuAbs loc rep fv (commandOpeningRec (k+1) args cmd)
-- Syntactic sugar
termOpeningRec k args (Semi loc rep ns xtor (MkSubstitutionI (args1,pcrep,args2)) tm) =
  let
    args1' = pctermOpeningRec k args <$> args1
    args2' = pctermOpeningRec k args <$> args2
  in
    Semi loc rep ns xtor (MkSubstitutionI (args1', pcrep, args2')) (termOpeningRec k args tm)
termOpeningRec k args (Dtor loc rep ns xt t (MkSubstitutionI (args1,pcrep,args2))) =
  let
    args1' = pctermOpeningRec k args <$> args1
    args2' = pctermOpeningRec k args <$> args2
  in
    Dtor loc rep ns xt (termOpeningRec k args t) (MkSubstitutionI (args1', pcrep, args2'))
termOpeningRec k args (CaseOf loc rep ns t cases) =
  CaseOf loc rep ns (termOpeningRec k args t) ((\pmcase -> pmcase { tmcase_term = termOpeningRec (k + 1) args pmcase.tmcase_term }) <$> cases)
termOpeningRec k args (CocaseOf loc rep ns t tmcases) = 
  CocaseOf loc rep ns (termOpeningRec k args t) ((\pmcase -> pmcase { tmcase_term = termOpeningRec (k + 1) args pmcase.tmcase_term }) <$> tmcases)
termOpeningRec k args (CaseI loc pcrep ns tmcasesI) =
  CaseI loc pcrep ns ((\pmcase -> pmcase { tmcasei_term = termOpeningRec (k + 1) args pmcase.tmcasei_term }) <$> tmcasesI)
termOpeningRec k args (CocaseI loc pcrep ns cocases) =
  CocaseI loc pcrep ns ((\pmcase -> pmcase { tmcasei_term = termOpeningRec (k + 1) args pmcase.tmcasei_term }) <$> cocases)
termOpeningRec k args (Lambda loc pcrep ns tm) = 
  Lambda loc pcrep ns (termOpeningRec (k+1) args tm)  
-- Primitive constructs
termOpeningRec _ _ lit@PrimLitI64{} = lit
termOpeningRec _ _ lit@PrimLitF64{} = lit
termOpeningRec _ _ lit@PrimLitChar{} = lit
termOpeningRec _ _ lit@PrimLitString{} = lit


commandOpeningRec :: Int -> Substitution -> Command -> Command
commandOpeningRec _ _ (ExitSuccess loc) =
  ExitSuccess loc
commandOpeningRec _ _ (ExitFailure loc) =
  ExitFailure loc
commandOpeningRec k args (Print loc t cmd) =
  Print loc (termOpeningRec k args t) (commandOpeningRec k args cmd)
commandOpeningRec k args (Read loc cns) =
  Read loc (termOpeningRec k args cns)
commandOpeningRec _ _ (Jump loc fv) =
  Jump loc fv
commandOpeningRec k args (Method loc mn cn ty subst) =
  Method loc mn cn ty (pctermOpeningRec k args <¢> subst)
commandOpeningRec k args (Apply loc t1 t2) =
  Apply loc (termOpeningRec k args t1) (termOpeningRec k args t2)
commandOpeningRec k args (PrimOp loc op subst) =
  PrimOp loc op (pctermOpeningRec k args <¢> subst)
commandOpeningRec k args (CaseOfCmd loc ns t cmdcases) =
  CaseOfCmd loc ns  (termOpeningRec k args t) $ map (\pmcase -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args pmcase.cmdcase_cmd }) cmdcases
commandOpeningRec k args (CaseOfI loc pcrep ns t tmcasesI) =
  CaseOfI loc pcrep ns (termOpeningRec k args t) ((\pmcase -> pmcase { tmcasei_term = termOpeningRec (k + 1) args pmcase.tmcasei_term }) <$> tmcasesI) 
commandOpeningRec k args (CocaseOfCmd loc ns t cmdcases) =
  CocaseOfCmd loc ns (termOpeningRec k args t) $ map (\pmcase -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args pmcase.cmdcase_cmd }) cmdcases
commandOpeningRec k args (CocaseOfI loc pcrep ns t tmcasesI) =
  CocaseOfI loc pcrep ns (termOpeningRec k args t) ((\pmcase -> pmcase { tmcasei_term = termOpeningRec (k + 1) args pmcase.tmcasei_term }) <$> tmcasesI) 


---------------------------------------------------------------------------------
-- Variable Closing
---------------------------------------------------------------------------------

pctermClosingRec :: Int -> [(PrdCns, FreeVarName)] -> PrdCnsTerm -> PrdCnsTerm
pctermClosingRec k vars (PrdTerm tm) = PrdTerm $ termClosingRec k vars tm
pctermClosingRec k vars (CnsTerm tm) = CnsTerm $ termClosingRec k vars tm

termClosingRec :: Int -> [(PrdCns, FreeVarName)] -> Term pc -> Term pc
-- Core constructs
termClosingRec _ _ bv@BoundVar {} = bv
termClosingRec k vars (FreeVar loc PrdRep v) = case (Prd,v) `elemIndex` vars of
                                                  Just ix -> BoundVar loc PrdRep (k, ix)
                                                  Nothing -> FreeVar loc PrdRep v
termClosingRec k vars (FreeVar loc CnsRep v) = case (Cns,v) `elemIndex` vars of
                                                  Just ix -> BoundVar loc CnsRep (k, ix)
                                                  Nothing -> FreeVar loc CnsRep v
termClosingRec k vars (Xtor loc pc ns xt subst) =
  Xtor loc pc ns xt (pctermClosingRec k vars <¢> subst)
termClosingRec k vars (XCase loc pc sn cases) =
  XCase loc pc sn $ map (\pmcase -> pmcase { cmdcase_cmd = commandClosingRec (k+1) vars pmcase.cmdcase_cmd }) cases
termClosingRec k vars (MuAbs loc pc fv cmd) =
  MuAbs loc pc fv (commandClosingRec (k+1) vars cmd)
-- Syntactic sugar
termClosingRec k args (Semi loc rep ns xt (MkSubstitutionI (args1,pcrep,args2)) t) = 
  let
    args1' = pctermClosingRec k args <$> args1
    args2' = pctermClosingRec k args <$> args2
  in
  Semi loc rep ns xt (MkSubstitutionI (args1',pcrep,args2')) (termClosingRec k args t)
termClosingRec k args (Dtor loc pc ns xt t (MkSubstitutionI (args1,pcrep,args2))) =
  let
    args1' = pctermClosingRec k args <$> args1
    args2' = pctermClosingRec k args <$> args2
  in
    Dtor loc pc ns xt (termClosingRec k args t) (MkSubstitutionI (args1', pcrep, args2'))
termClosingRec k args (CaseOf loc rep ns t cases) =
  CaseOf loc rep ns (termClosingRec k args t) ((\pmcase -> pmcase { tmcase_term = termClosingRec (k + 1) args pmcase.tmcase_term }) <$> cases)
termClosingRec k args (CocaseOf loc rep ns t tmcases) = 
  CocaseOf loc rep ns (termClosingRec k args t) ((\pmcase -> pmcase { tmcase_term = termClosingRec (k + 1) args pmcase.tmcase_term }) <$> tmcases) 
termClosingRec k args (CaseI loc pcrep ns tmcasesI) = 
  CaseI loc pcrep ns ((\pmcase -> pmcase { tmcasei_term = termClosingRec (k + 1) args pmcase.tmcasei_term }) <$> tmcasesI) 
termClosingRec k args (CocaseI loc pcrep ns cocases) =
  CocaseI loc pcrep ns ((\pmcase -> pmcase { tmcasei_term = termClosingRec (k + 1) args pmcase.tmcasei_term }) <$> cocases)
termClosingRec k args (Lambda loc pcrep fv tm) = 
  Lambda loc pcrep fv (termClosingRec (k+1) args tm)  
-- Primitive constructs
termClosingRec _ _ lit@PrimLitI64{} = lit
termClosingRec _ _ lit@PrimLitF64{} = lit
termClosingRec _ _ lit@PrimLitChar{} = lit
termClosingRec _ _ lit@PrimLitString{} = lit


commandClosingRec :: Int -> [(PrdCns, FreeVarName)] -> Command -> Command
commandClosingRec _ _ (ExitSuccess ext) =
  ExitSuccess ext
commandClosingRec _ _ (ExitFailure ext) =
  ExitFailure ext
commandClosingRec _ _ (Jump ext fv) =
  Jump ext fv
commandClosingRec k args (Method ext mn cn ty subst) =
  Method ext mn cn ty (pctermClosingRec k args <¢> subst)
commandClosingRec k args (Print ext t cmd) =
  Print ext (termClosingRec k args t) (commandClosingRec k args cmd)
commandClosingRec k args (Read ext cns) =
  Read ext (termClosingRec k args cns)
commandClosingRec k args (Apply ext t1 t2) =
  Apply ext (termClosingRec k args t1) (termClosingRec k args t2)
commandClosingRec k args (PrimOp ext op subst) =
  PrimOp ext op (pctermClosingRec k args <¢> subst)
commandClosingRec k args (CaseOfCmd loc ns t cmdcases) =
  CaseOfCmd loc ns  (termClosingRec k args t) $ map (\pmcase -> pmcase { cmdcase_cmd = commandClosingRec (k+1) args pmcase.cmdcase_cmd }) cmdcases
commandClosingRec k args (CaseOfI loc pcrep ns t tmcasesI) =
  CaseOfI loc pcrep ns (termClosingRec k args t) ((\pmcase -> pmcase { tmcasei_term = termClosingRec (k + 1) args pmcase.tmcasei_term }) <$> tmcasesI) 
commandClosingRec k args (CocaseOfCmd loc ns t cmdcases) =
  CocaseOfCmd loc ns (termClosingRec k args t) $ map (\pmcase -> pmcase { cmdcase_cmd = commandClosingRec (k+1) args pmcase.cmdcase_cmd }) cmdcases
commandClosingRec k args (CocaseOfI loc pcrep ns t tmcasesI) =
  CocaseOfI loc pcrep ns (termClosingRec k args t) ((\pmcase -> pmcase { tmcasei_term = termClosingRec (k + 1) args pmcase.tmcasei_term }) <$> tmcasesI) 

instance LocallyNameless Substitution [(PrdCns, FreeVarName)] Command where
  openRec  = commandOpeningRec
  closeRec = commandClosingRec

instance LocallyNameless Substitution [(PrdCns, FreeVarName)] (Term pc) where
  openRec  = termOpeningRec
  closeRec = termClosingRec
