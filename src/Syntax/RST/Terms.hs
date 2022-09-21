module Syntax.RST.Terms
  ( -- Terms
    Term(..)
  , PrdCnsTerm(..)
  , Substitution(..)
  , SubstitutionI(..)
  , Pattern(..)
  , PatternI(..)
  , TermCase(..)
  , TermCaseI(..)
  , CmdCase(..)
  , InstanceCase(..)
  , Command(..)
  , PrimitiveOp(..)
   -- Functions
  ) where

import Data.List (elemIndex)

import Loc ( Loc )
import Syntax.CST.Names
    ( ClassName, FreeVarName, Index, MethodName, XtorName )
import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types ( PrdCnsRep(..), PrdCns(..) )
import Syntax.LocallyNameless (LocallyNameless (..))

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
  Method :: Loc -> MethodName -> ClassName -> Substitution -> Command
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
termOpeningRec k subst bv@(BoundVar _ pcrep (i,j)) | i == k    = case (pcrep, unSubstitution subst !! j) of
                                                                      (PrdRep, PrdTerm tm) -> tm
                                                                      (CnsRep, CnsTerm tm) -> tm
                                                                      t                    -> error $ "termOpeningRec BOOM: " ++ show t
                                                   | otherwise = bv
termOpeningRec _ _ fv@FreeVar {}= fv
termOpeningRec k args (Xtor loc rep ns xt subst) =
  Xtor loc rep ns xt (MkSubstitution (pctermOpeningRec k args <$> unSubstitution subst))
termOpeningRec k args (XCase loc rep ns cases) =
  XCase loc rep ns $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args cmdcase_cmd }) cases
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
  CaseOf loc rep ns (termOpeningRec k args t) ((\pmcase@MkTermCase { tmcase_term } -> pmcase { tmcase_term = termOpeningRec (k + 1) args tmcase_term }) <$> cases)
termOpeningRec k args (CocaseOf loc rep ns t tmcases) = 
  CocaseOf loc rep ns (termOpeningRec k args t) ((\pmcase@MkTermCase { tmcase_term } -> pmcase { tmcase_term = termOpeningRec (k + 1) args tmcase_term }) <$> tmcases)
termOpeningRec k args (CaseI loc pcrep ns tmcasesI) =
  CaseI loc pcrep ns ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termOpeningRec (k + 1) args tmcasei_term }) <$> tmcasesI)
termOpeningRec k args (CocaseI loc pcrep ns cocases) =
  CocaseI loc pcrep ns ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termOpeningRec (k + 1) args tmcasei_term }) <$> cocases)
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
commandOpeningRec k args (Method loc mn cn subst) =
  Method loc mn cn (MkSubstitution (pctermOpeningRec k args <$> unSubstitution subst))
commandOpeningRec k args (Apply loc t1 t2) =
  Apply loc (termOpeningRec k args t1) (termOpeningRec k args t2)
commandOpeningRec k args (PrimOp loc op subst) =
  PrimOp loc op (MkSubstitution (pctermOpeningRec k args <$> unSubstitution subst))
commandOpeningRec k args (CaseOfCmd loc ns t cmdcases) =
  CaseOfCmd loc ns  (termOpeningRec k args t) $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args cmdcase_cmd }) cmdcases
commandOpeningRec k args (CaseOfI loc pcrep ns t tmcasesI) =
  CaseOfI loc pcrep ns (termOpeningRec k args t) ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termOpeningRec (k + 1) args tmcasei_term }) <$> tmcasesI) 
commandOpeningRec k args (CocaseOfCmd loc ns t cmdcases) =
  CocaseOfCmd loc ns (termOpeningRec k args t) $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args cmdcase_cmd }) cmdcases
commandOpeningRec k args (CocaseOfI loc pcrep ns t tmcasesI) =
  CocaseOfI loc pcrep ns (termOpeningRec k args t) ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termOpeningRec (k + 1) args tmcasei_term }) <$> tmcasesI) 


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
  Xtor loc pc ns xt (MkSubstitution (pctermClosingRec k vars <$> unSubstitution subst))
termClosingRec k vars (XCase loc pc sn cases) =
  XCase loc pc sn $ map (\pmcase@MkCmdCase { cmdcase_cmd } -> pmcase { cmdcase_cmd = commandClosingRec (k+1) vars cmdcase_cmd }) cases
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
  CaseOf loc rep ns (termClosingRec k args t) ((\pmcase@MkTermCase { tmcase_term } -> pmcase { tmcase_term = termClosingRec (k + 1) args tmcase_term }) <$> cases)
termClosingRec k args (CocaseOf loc rep ns t tmcases) = 
  CocaseOf loc rep ns (termClosingRec k args t) ((\pmcase@MkTermCase { tmcase_term } -> pmcase { tmcase_term = termClosingRec (k + 1) args tmcase_term }) <$> tmcases) 
termClosingRec k args (CaseI loc pcrep ns tmcasesI) = 
  CaseI loc pcrep ns ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termClosingRec (k + 1) args tmcasei_term }) <$> tmcasesI) 
termClosingRec k args (CocaseI loc pcrep ns cocases) =
  CocaseI loc pcrep ns ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termClosingRec (k + 1) args tmcasei_term }) <$> cocases)
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
commandClosingRec k args (Method ext mn cn subst) =
  Method ext mn cn (MkSubstitution (pctermClosingRec k args <$> unSubstitution subst))
commandClosingRec k args (Print ext t cmd) =
  Print ext (termClosingRec k args t) (commandClosingRec k args cmd)
commandClosingRec k args (Read ext cns) =
  Read ext (termClosingRec k args cns)
commandClosingRec k args (Apply ext t1 t2) =
  Apply ext (termClosingRec k args t1) (termClosingRec k args t2)
commandClosingRec k args (PrimOp ext op subst) =
  PrimOp ext op (MkSubstitution (pctermClosingRec k args <$> unSubstitution subst))
commandClosingRec k args (CaseOfCmd loc ns t cmdcases) =
  CaseOfCmd loc ns  (termClosingRec k args t) $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandClosingRec (k+1) args cmdcase_cmd }) cmdcases
commandClosingRec k args (CaseOfI loc pcrep ns t tmcasesI) =
  CaseOfI loc pcrep ns (termClosingRec k args t) ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termClosingRec (k + 1) args tmcasei_term }) <$> tmcasesI) 
commandClosingRec k args (CocaseOfCmd loc ns t cmdcases) =
  CocaseOfCmd loc ns (termClosingRec k args t) $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandClosingRec (k+1) args cmdcase_cmd }) cmdcases
commandClosingRec k args (CocaseOfI loc pcrep ns t tmcasesI) =
  CocaseOfI loc pcrep ns (termClosingRec k args t) ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termClosingRec (k + 1) args tmcasei_term }) <$> tmcasesI) 

instance LocallyNameless Substitution [(PrdCns, FreeVarName)] Command where
  openRec  = commandOpeningRec
  closeRec = commandClosingRec

instance LocallyNameless Substitution [(PrdCns, FreeVarName)] (Term pc) where
  openRec  = termOpeningRec
  closeRec = termClosingRec
