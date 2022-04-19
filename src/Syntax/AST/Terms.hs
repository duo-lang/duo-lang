module Syntax.AST.Terms
  ( -- Terms
    Term(..)
  , PrdCnsTerm(..)
  , Substitution
  , SubstitutionI
  , TermCase(..)
  , TermCaseI(..)
  , CmdCase(..)
  , Command(..)
  -- Functions
  , commandClosing
  , shiftCmd
  , getTypeTerm
  , getTypArgs
  , commandOpening
  , termLocallyClosed
  ) where

import Data.List (elemIndex)
import Data.Maybe (fromJust, isJust)
import Data.Text qualified as T

import Utils
import Errors
import Syntax.Common
import Syntax.RST.Types

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

deriving instance Eq PrdCnsTerm
deriving instance Show PrdCnsTerm

instance Zonk PrdCnsTerm where
  zonk bisubst (PrdTerm tm) = PrdTerm (zonk bisubst tm)
  zonk bisubst (CnsTerm tm) = CnsTerm (zonk bisubst tm)

type Substitution = [PrdCnsTerm]

-- | A SubstitutionI is like a substitution where one of the arguments has been
-- replaced by an implicit argument. The following convention for the use of the
-- `pc` parameter is used:
--
-- SubstitutionI Prd = ... [*] ...
-- SubstitutionI Cns = ... (*) ...
type SubstitutionI (pc :: PrdCns) = (Substitution, PrdCnsRep pc, Substitution)

---------------------------------------------------------------------------------
-- Pattern/copattern match cases
---------------------------------------------------------------------------------

-- | Represents one case in a pattern match or copattern match.
--
--        X(x_1,...,x_n) => e
--        ^ ^^^^^^^^^^^     ^
--        |      |          |
--        |  tmcase_args  tmcase_term
--        |
--    tmcase_name
--
data TermCase (pc :: PrdCns) = MkTermCase
  { tmcase_loc  :: Loc
  , tmcase_name :: XtorName
  , tmcase_args :: [(PrdCns, Maybe FreeVarName)]
  , tmcase_term :: Term pc
  }

instance Zonk (TermCase pc) where
  zonk bisubst (MkTermCase loc nm args tm) =
    MkTermCase loc nm args (zonk bisubst tm)

deriving instance Eq (TermCase pc)
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
  , tmcasei_name :: XtorName
  -- | The pattern arguments
  -- The empty tuple stands for the implicit argument (*)
  , tmcasei_args :: ([(PrdCns, Maybe FreeVarName)], (), [(PrdCns, Maybe FreeVarName)])
  , tmcasei_term :: Term pc
  }

instance Zonk (TermCaseI pc) where
  zonk bisubst (MkTermCaseI loc nm args tm) =
    MkTermCaseI loc nm args (zonk bisubst tm)

deriving instance Eq (TermCaseI pc)
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
  , cmdcase_name :: XtorName
  , cmdcase_args :: [(PrdCns, Maybe FreeVarName)]
  , cmdcase_cmd  :: Command
  }

instance Zonk CmdCase where
  zonk bisubst (MkCmdCase loc nm args cmd) =
    MkCmdCase loc nm args (zonk bisubst cmd)

deriving instance Eq CmdCase
deriving instance Show CmdCase

---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

-- | A symmetric term.
-- The `bs` parameter is used to store additional information at binding sites.
data Term (pc :: PrdCns) where
  ---------------------------------------------------------------------------------
  -- Core constructs
  ---------------------------------------------------------------------------------
  -- | A bound variable in the locally nameless system.
  BoundVar :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> Index -> Term pc
  -- | A free variable in the locally nameless system.
  FreeVar :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> FreeVarName -> Term pc
  -- | A constructor or destructor.
  -- If the first argument is `PrdRep` it is a constructor, a destructor otherwise.
  Xtor :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> XtorName -> Substitution -> Term pc
  -- | A pattern or copattern match.
  -- If the first argument is `PrdRep` it is a copattern match, a pattern match otherwise.
  XCase :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> [CmdCase] -> Term pc
  -- | A Mu or TildeMu abstraction:
  --
  --  mu k.c    =   MuAbs PrdRep c
  -- ~mu x.c    =   MuAbs CnsRep c
  MuAbs :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> Maybe FreeVarName -> Command -> Term pc
  ---------------------------------------------------------------------------------
  -- Syntactic Sugar
  ---------------------------------------------------------------------------------
  -- The two dual constructs "Dtor" and "Semi"
  --
  -- Dtor:
  --  prd.Dtor(args)
  -- Semi:
  --  C(args).cns
  Semi :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> XtorName -> SubstitutionI pc -> Term Cns -> Term pc
  Dtor :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> XtorName -> Term Prd -> SubstitutionI pc -> Term pc
  -- The dual constructs
  -- case e of 
  -- case e of { ... }
  --
  CaseOf   :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> Term Prd -> [TermCase pc] -> Term pc
  CocaseOf :: Loc -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> NominalStructural -> Term Cns -> [TermCase pc] -> Term pc

  CaseI   :: Loc -> PrdCnsRep pc -> Typ Neg -> NominalStructural -> [TermCaseI pc] -> Term Cns
  CocaseI :: Loc -> PrdCnsRep pc -> Typ Pos -> NominalStructural -> [TermCaseI pc] -> Term Prd
  ---------------------------------------------------------------------------------
  -- Primitive constructs
  ---------------------------------------------------------------------------------
  PrimLitI64 :: Loc -> Integer -> Term Prd
  PrimLitF64 :: Loc -> Double -> Term Prd

instance Eq (Term pc) where
  (==) = undefined

deriving instance Show (Term pc)

instance Zonk (Term pc) where
  zonk bisubst (BoundVar loc rep ty idx) =
    BoundVar loc rep (zonk bisubst ty) idx
  zonk bisubst (FreeVar loc rep ty nm)  =
    FreeVar loc rep (zonk bisubst ty) nm
  zonk bisubst (Xtor loc rep ty ns xt subst) =
    Xtor loc rep (zonk bisubst ty) ns xt (zonk bisubst <$> subst)
  zonk bisubst (XCase loc rep ty ns cases) =
    XCase loc rep (zonk bisubst ty) ns (zonk bisubst <$> cases)
  zonk bisubst (MuAbs loc rep ty fv cmd) =
    MuAbs loc rep (zonk bisubst ty) fv (zonk bisubst cmd)
  zonk bisubst (Dtor loc rep ty ns xt prd (subst1,pcrep,subst2)) =
    Dtor loc rep (zonk bisubst ty) ns xt (zonk bisubst prd) (zonk bisubst <$> subst1,pcrep,zonk bisubst <$> subst2)
  zonk bisubst (CaseOf loc rep ty ns prd cases) =
    CaseOf loc rep (zonk bisubst ty) ns (zonk bisubst prd) (zonk bisubst <$> cases)
  zonk bisubst (CocaseI loc pcrep ty ns cases) =
    CocaseI loc pcrep (zonk bisubst ty) ns (zonk bisubst <$> cases)
  zonk bisubst (CaseI loc pcrep ty ns cases) =
    CaseI loc pcrep (zonk bisubst ty) ns (zonk bisubst <$> cases)
  zonk bisubst (Semi loc rep ty ns xt (subst1,pcrep,subst2) t) =
    Semi loc rep (zonk bisubst ty) ns xt (zonk bisubst <$> subst1,pcrep,zonk bisubst <$> subst2) (zonk bisubst t)
  zonk bisubst (CocaseOf loc rep ty ns t cases) =
    CocaseOf loc rep (zonk bisubst ty) ns (zonk bisubst t) (zonk bisubst <$> cases) 
  zonk _ lit@PrimLitI64{} = lit
  zonk _ lit@PrimLitF64{} = lit



getTypeTerm :: forall pc. Term pc -> Typ (PrdCnsToPol pc)
getTypeTerm (BoundVar _ _ annot _)   = annot
getTypeTerm (FreeVar  _ _ annot _)   = annot
getTypeTerm (Xtor _ _ annot _ _ _)   = annot
getTypeTerm (XCase _ _ annot _ _)   = annot
getTypeTerm (MuAbs _ _ annot _ _)    = annot
getTypeTerm (Dtor _ _ annot _ _ _ _) = annot
getTypeTerm (CaseOf _ _ annot  _ _ _)     = annot
getTypeTerm (CocaseI _ _ annot _ _)     = annot
getTypeTerm (PrimLitI64 _ _)         = TyPrim defaultLoc PosRep I64
getTypeTerm (PrimLitF64 _ _)         = TyPrim defaultLoc PosRep F64
getTypeTerm (CaseI _ _ annot _ _) = annot
getTypeTerm (Semi _ _ annot _ _ _ _) = annot
getTypeTerm (CocaseOf _ _ annot _ _ _) = annot

getTypArgs :: Substitution -> LinearContext Pos
getTypArgs subst = getTypArgs'' <$> subst
   where
     getTypArgs'' (PrdTerm tm) = PrdCnsType PrdRep $ getTypeTerm tm
     getTypArgs'' (CnsTerm tm) = PrdCnsType CnsRep $ getTypeTerm tm


---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

-- | An executable command.
data Command where
  -- | A producer applied to a consumer:
  --
  --   p >> c
  Apply  :: Loc -> Maybe MonoKind -> Term Prd -> Term Cns -> Command
  Print  :: Loc -> Term Prd -> Command -> Command
  Read   :: Loc -> Term Cns -> Command
  Jump   :: Loc -> FreeVarName -> Command
  ExitSuccess :: Loc -> Command
  ExitFailure :: Loc -> Command
  PrimOp :: Loc -> PrimitiveType -> PrimitiveOp -> Substitution -> Command
  CaseOfCmd :: Loc -> NominalStructural -> Term Prd -> [CmdCase] -> Command
  CaseOfI :: Loc -> PrdCnsRep pc -> NominalStructural -> Term Prd -> [TermCaseI pc] -> Command
  CocaseOfCmd :: Loc -> NominalStructural -> Term Cns -> [CmdCase] -> Command
  CocaseOfI :: Loc -> PrdCnsRep pc -> NominalStructural -> Term Cns -> [TermCaseI pc] -> Command

deriving instance Show Command
instance Eq Command where
  (==) = undefined

instance Zonk Command where
  zonk bisubst (Apply ext kind prd cns) =
    Apply ext kind (zonk bisubst prd) (zonk bisubst cns)
  zonk bisubst (Print ext prd cmd) =
    Print ext (zonk bisubst prd) (zonk bisubst cmd)
  zonk bisubst (Read ext cns) =
    Read ext (zonk bisubst cns)
  zonk _ (Jump ext fv) =
    Jump ext fv
  zonk _ (ExitSuccess ext) =
    ExitSuccess ext
  zonk _ (ExitFailure ext) =
    ExitFailure ext
  zonk bisubst (PrimOp ext pt op subst) =
    PrimOp ext pt op (zonk bisubst <$> subst)
  zonk bisubst (CaseOfCmd loc ns t cases) =
    CaseOfCmd loc ns (zonk bisubst t) (zonk bisubst <$> cases) 
  zonk bisubst (CaseOfI loc pcrep ns t cases) =
    CaseOfI loc pcrep ns (zonk bisubst t) (zonk bisubst <$> cases) 
  zonk bisubst (CocaseOfCmd loc ns t cases) =
    CocaseOfCmd loc ns (zonk bisubst t) (zonk bisubst <$> cases) 
  zonk bisubst (CocaseOfI loc pcrep ns t cases) =
    CocaseOfI loc pcrep ns (zonk bisubst t) (zonk bisubst <$> cases) 



---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

pctermOpeningRec :: Int -> Substitution -> PrdCnsTerm -> PrdCnsTerm
pctermOpeningRec k subst (PrdTerm tm) = PrdTerm $ termOpeningRec k subst tm
pctermOpeningRec k subst (CnsTerm tm) = CnsTerm $ termOpeningRec k subst tm


termOpeningRec :: Int -> Substitution -> Term pc -> Term pc
termOpeningRec k subst bv@(BoundVar _ pcrep _ (i,j)) | i == k    = case (pcrep, subst !! j) of
                                                                      (PrdRep, PrdTerm tm) -> tm
                                                                      (CnsRep, CnsTerm tm) -> tm
                                                                      _                    -> error "termOpeningRec BOOM"
                                                   | otherwise = bv
termOpeningRec _ _ fv@(FreeVar _ _ _ _)       = fv
termOpeningRec k args (Xtor loc rep annot ns xt subst) =
  Xtor loc rep annot ns xt (pctermOpeningRec k args <$> subst)
termOpeningRec k args (XCase loc rep annot ns cases) =
  XCase loc rep annot ns $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args cmdcase_cmd }) cases
termOpeningRec k args (MuAbs loc rep annot fv cmd) =
  MuAbs loc rep annot fv (commandOpeningRec (k+1) args cmd)
-- ATerms
termOpeningRec k args (Dtor loc rep annot ns xt t (args1,pcrep,args2)) =
  let
    args1' = pctermOpeningRec k args <$> args1
    args2' = pctermOpeningRec k args <$> args2
  in
    Dtor loc rep annot ns xt (termOpeningRec k args t) (args1', pcrep, args2')
termOpeningRec k args (CaseOf loc rep annot ns t cases) =
  CaseOf loc rep annot ns (termOpeningRec k args t) ((\pmcase@MkTermCase { tmcase_term } -> pmcase { tmcase_term = termOpeningRec (k + 1) args tmcase_term }) <$> cases)
termOpeningRec k args (CocaseI loc pcrep annot ns cocases) =
  CocaseI loc pcrep annot ns ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termOpeningRec (k + 1) args tmcasei_term }) <$> cocases)
termOpeningRec k args (CaseI loc pcrep annot ns tmcasesI) =
  CaseI loc pcrep annot ns ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termOpeningRec (k + 1) args tmcasei_term }) <$> tmcasesI)
termOpeningRec k args (Semi loc rep annot ns xtor (args1,pcrep,args2) tm) =
  let
    args1' = pctermOpeningRec k args <$> args1
    args2' = pctermOpeningRec k args <$> args2
  in
    Semi loc rep annot ns xtor (args1', pcrep, args2') (termOpeningRec k args tm)

termOpeningRec k args (CocaseOf loc rep annot ns t tmcases) = 
  CocaseOf loc rep annot ns (termOpeningRec k args t) ((\pmcase@MkTermCase { tmcase_term } -> pmcase { tmcase_term = termOpeningRec (k + 1) args tmcase_term }) <$> tmcases)  
termOpeningRec _ _ lit@PrimLitI64{} = lit
termOpeningRec _ _ lit@PrimLitF64{} = lit

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
commandOpeningRec k args (Apply loc kind t1 t2) =
  Apply loc kind (termOpeningRec k args t1) (termOpeningRec k args t2)
commandOpeningRec k args (PrimOp loc pt op subst) =
  PrimOp loc pt op (pctermOpeningRec k args <$> subst)
commandOpeningRec k args (CaseOfCmd loc ns t cmdcases) =
  CaseOfCmd loc ns  (termOpeningRec k args t) $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args cmdcase_cmd }) cmdcases
commandOpeningRec k args (CaseOfI loc pcrep ns t tmcasesI) =
  CaseOfI loc pcrep ns (termOpeningRec k args t) ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termOpeningRec (k + 1) args tmcasei_term }) <$> tmcasesI) 
commandOpeningRec k args (CocaseOfCmd loc ns t cmdcases) =
  CocaseOfCmd loc ns (termOpeningRec k args t) $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args cmdcase_cmd }) cmdcases
commandOpeningRec k args (CocaseOfI loc pcrep ns t tmcasesI) =
  CocaseOfI loc pcrep ns (termOpeningRec k args t) ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termOpeningRec (k + 1) args tmcasei_term }) <$> tmcasesI) 

commandOpening :: Substitution -> Command -> Command
commandOpening = commandOpeningRec 0

---------------------------------------------------------------------------------
-- Variable Closing
---------------------------------------------------------------------------------

pctermClosingRec :: Int -> [(PrdCns, FreeVarName)] -> PrdCnsTerm -> PrdCnsTerm
pctermClosingRec k vars (PrdTerm tm) = PrdTerm $ termClosingRec k vars tm
pctermClosingRec k vars (CnsTerm tm) = CnsTerm $ termClosingRec k vars tm

termClosingRec :: Int -> [(PrdCns, FreeVarName)] -> Term pc -> Term pc
termClosingRec _ _ bv@(BoundVar _ _ _ _) = bv
termClosingRec k vars (FreeVar loc PrdRep annot v) | isJust ((Prd,v) `elemIndex` vars) = BoundVar loc PrdRep annot (k, fromJust ((Prd,v) `elemIndex` vars))
                                                   | otherwise = FreeVar loc PrdRep annot v
termClosingRec k vars (FreeVar loc CnsRep annot v) | isJust ((Cns,v) `elemIndex` vars) = BoundVar loc CnsRep annot (k, fromJust ((Cns,v) `elemIndex` vars))
                                                   | otherwise = FreeVar loc CnsRep annot v
termClosingRec k vars (Xtor loc pc annot ns xt subst) =
  Xtor loc pc annot ns xt (pctermClosingRec k vars <$> subst)
termClosingRec k vars (XCase loc pc annot sn cases) =
  XCase loc pc annot sn $ map (\pmcase@MkCmdCase { cmdcase_cmd } -> pmcase { cmdcase_cmd = commandClosingRec (k+1) vars cmdcase_cmd }) cases
termClosingRec k vars (MuAbs loc pc annot fv cmd) =
  MuAbs loc pc annot fv (commandClosingRec (k+1) vars cmd)
-- ATerms
termClosingRec k args (Dtor loc pc annot ns xt t (args1,pcrep,args2)) =
  let
    args1' = pctermClosingRec k args <$> args1
    args2' = pctermClosingRec k args <$> args2
  in
    Dtor loc pc annot ns xt (termClosingRec k args t) (args1', pcrep, args2')
termClosingRec k args (CaseOf loc rep annot ns t cases) =
  CaseOf loc rep annot ns (termClosingRec k args t) ((\pmcase@MkTermCase { tmcase_term } -> pmcase { tmcase_term = termClosingRec (k + 1) args tmcase_term }) <$> cases)
termClosingRec k args (CocaseI loc pcrep annot ns cocases) =
  CocaseI loc pcrep annot ns ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termClosingRec (k + 1) args tmcasei_term }) <$> cocases)
termClosingRec k args (CaseI loc pcrep annot ns tmcasesI) = 
  CaseI loc pcrep annot ns ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termClosingRec (k + 1) args tmcasei_term }) <$> tmcasesI) 
termClosingRec k args (Semi loc rep annot ns xt (args1,pcrep,args2) t) = 
  let
    args1' = pctermClosingRec k args <$> args1
    args2' = pctermClosingRec k args <$> args2
  in
  Semi loc rep annot ns xt (args1',pcrep,args2') (termClosingRec k args t)

termClosingRec k args (CocaseOf loc rep annot ns t tmcases) = 
  CocaseOf loc rep annot ns (termClosingRec k args t) ((\pmcase@MkTermCase { tmcase_term } -> pmcase { tmcase_term = termClosingRec (k + 1) args tmcase_term }) <$> tmcases) 
termClosingRec _ _ lit@PrimLitI64{} = lit
termClosingRec _ _ lit@PrimLitF64{} = lit


commandClosingRec :: Int -> [(PrdCns, FreeVarName)] -> Command -> Command
commandClosingRec _ _ (ExitSuccess ext) =
  ExitSuccess ext
commandClosingRec _ _ (ExitFailure ext) =
  ExitFailure ext
commandClosingRec _ _ (Jump ext fv) =
  Jump ext fv
commandClosingRec k args (Print ext t cmd) =
  Print ext (termClosingRec k args t) (commandClosingRec k args cmd)
commandClosingRec k args (Read ext cns) =
  Read ext (termClosingRec k args cns)
commandClosingRec k args (Apply ext kind t1 t2) =
  Apply ext kind (termClosingRec k args t1) (termClosingRec k args t2)
commandClosingRec k args (PrimOp ext pt op subst) =
  PrimOp ext pt op (pctermClosingRec k args <$> subst)
commandClosingRec k args (CaseOfCmd loc ns t cmdcases) =
  CaseOfCmd loc ns  (termClosingRec k args t) $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandClosingRec (k+1) args cmdcase_cmd }) cmdcases
commandClosingRec k args (CaseOfI loc pcrep ns t tmcasesI) =
  CaseOfI loc pcrep ns (termClosingRec k args t) ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termClosingRec (k + 1) args tmcasei_term }) <$> tmcasesI) 
commandClosingRec k args (CocaseOfCmd loc ns t cmdcases) =
  CocaseOfCmd loc ns (termClosingRec k args t) $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandClosingRec (k+1) args cmdcase_cmd }) cmdcases
commandClosingRec k args (CocaseOfI loc pcrep ns t tmcasesI) =
  CocaseOfI loc pcrep ns (termClosingRec k args t) ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termClosingRec (k + 1) args tmcasei_term }) <$> tmcasesI) 

commandClosing :: [(PrdCns, FreeVarName)] -> Command -> Command
commandClosing = commandClosingRec 0

---------------------------------------------------------------------------------
-- Check for locally closedness
---------------------------------------------------------------------------------

checkIfBound :: [[(PrdCns,a)]] -> PrdCnsRep pc -> Index -> Either Error ()
checkIfBound env rep  (i, j) | i >= length env = Left $ OtherError Nothing $ "Variable " <> T.pack (show (i,j)) <> " is not bound (Outer index)"
                             | otherwise = checkIfBoundInner (env !! i) rep (i,j)

checkIfBoundInner :: [(PrdCns,a)] -> PrdCnsRep pc -> Index -> Either Error ()
checkIfBoundInner vars PrdRep idx@(_,j) =
  if j < length vars
    then case vars !! j of
      (Prd,_) -> return ()
      (Cns,_) -> Left $ OtherError Nothing $ "Variable " <> T.pack (show idx) <> " is not bound to Producer"
    else Left $ OtherError Nothing $ "Variable " <> T.pack (show idx) <> " is not bound (Inner index)"
checkIfBoundInner vars CnsRep idx@(_,j) =
  if j < length vars
    then case vars !! j of
      (Cns,_) -> return ()
      (Prd,_) -> Left $ OtherError Nothing $ "Variable " <> T.pack (show idx) <> " is not bound to Consumer"
    else Left $ OtherError Nothing $ "Variable " <> T.pack (show idx) <> " is not bound (Inner index)"

pctermLocallyClosedRec :: [[(PrdCns, ())]] -> PrdCnsTerm -> Either Error ()
pctermLocallyClosedRec env (PrdTerm tm) = termLocallyClosedRec env tm
pctermLocallyClosedRec env (CnsTerm tm) = termLocallyClosedRec env tm

termLocallyClosedRec :: [[(PrdCns,())]] -> Term pc -> Either Error ()
termLocallyClosedRec env (BoundVar _ pc _ idx) = checkIfBound env pc idx
termLocallyClosedRec _ (FreeVar _ _ _ _) = Right ()
termLocallyClosedRec env (Xtor _ _ _ _ _ subst) = do
  sequence_ (pctermLocallyClosedRec env <$> subst)
termLocallyClosedRec env (XCase _ _ _ _ cases) = do
  sequence_ ((\MkCmdCase { cmdcase_cmd, cmdcase_args } -> commandLocallyClosedRec (((\(x,_) -> (x,())) <$> cmdcase_args) : env) cmdcase_cmd) <$> cases)
termLocallyClosedRec env (MuAbs _ PrdRep _ _ cmd) = commandLocallyClosedRec ([(Cns,())] : env) cmd
termLocallyClosedRec env (MuAbs _ CnsRep _ _ cmd) = commandLocallyClosedRec ([(Prd,())] : env) cmd
termLocallyClosedRec env (Dtor _ _ _ _ _ e (args1,_,args2)) = do
  termLocallyClosedRec env e
  sequence_ (pctermLocallyClosedRec env <$> args1)
  sequence_ (pctermLocallyClosedRec env <$> args2)
termLocallyClosedRec env (CaseOf _ _ _ _ e cases) = do
  termLocallyClosedRec env e
  sequence_ (termCaseLocallyClosedRec env <$> cases)
termLocallyClosedRec env (CocaseI _ _ _ _ cases) =
  sequence_ (termCaseILocallyClosedRec env <$> cases)
termLocallyClosedRec env (CaseI _ _ _ _ tmcasesI) = 
  sequence_ (termCaseILocallyClosedRec env <$> tmcasesI)
termLocallyClosedRec env (Semi _ _ _ _ _ (args1,_,args2) t) = do 
  termLocallyClosedRec env t
  sequence_ (pctermLocallyClosedRec env <$> args1)
  sequence_ (pctermLocallyClosedRec env <$> args2)
termLocallyClosedRec env (CocaseOf _ _ _ _ t tmcases) = do 
  termLocallyClosedRec env t
  sequence_ (termCaseLocallyClosedRec env <$> tmcases)
  
termLocallyClosedRec _ (PrimLitI64 _ _) = Right ()
termLocallyClosedRec _ (PrimLitF64 _ _) = Right ()

termCaseLocallyClosedRec :: [[(PrdCns,())]] -> TermCase pc -> Either Error ()
termCaseLocallyClosedRec env (MkTermCase _ _ args e) = do
  termLocallyClosedRec (((\(x,_) -> (x,())) <$> args):env) e

termCaseILocallyClosedRec :: [[(PrdCns,())]] -> TermCaseI pc -> Either Error ()
termCaseILocallyClosedRec env (MkTermCaseI _ _ (as1, (), as2) e) =
  let newArgs = (\(x,_) -> (x,())) <$> as1 ++ [(Cns, Nothing)] ++ as2 in
  termLocallyClosedRec (newArgs:env) e

cmdCaseLocallyClosedRec :: [[(PrdCns,())]] -> CmdCase -> Either Error ()
cmdCaseLocallyClosedRec env (MkCmdCase _ _ args cmd)= do 
  commandLocallyClosedRec (((\(x,_) -> (x,())) <$> args):env) cmd

commandLocallyClosedRec :: [[(PrdCns,())]] -> Command -> Either Error ()
commandLocallyClosedRec _ (ExitSuccess _) = Right ()
commandLocallyClosedRec _ (ExitFailure _) = Right ()
commandLocallyClosedRec _ (Jump _ _) = Right ()
commandLocallyClosedRec env (Print _ t cmd) = termLocallyClosedRec env t >> commandLocallyClosedRec env cmd
commandLocallyClosedRec env (Read _ cns) = termLocallyClosedRec env cns
commandLocallyClosedRec env (Apply _ _ t1 t2) = termLocallyClosedRec env t1 >> termLocallyClosedRec env t2
commandLocallyClosedRec env (PrimOp _ _ _ subst) = sequence_ $ pctermLocallyClosedRec env <$> subst
commandLocallyClosedRec env (CaseOfCmd _ _ t cmdcases) = do 
  termLocallyClosedRec env t
  sequence_ (cmdCaseLocallyClosedRec env <$> cmdcases)
commandLocallyClosedRec env (CaseOfI _ _ _ t tmcasesI) = do
  termLocallyClosedRec env t
  sequence_ (termCaseILocallyClosedRec env <$> tmcasesI)
commandLocallyClosedRec env (CocaseOfCmd _ _ t cmdcases) = do 
  termLocallyClosedRec env t
  sequence_ (cmdCaseLocallyClosedRec env <$> cmdcases)
commandLocallyClosedRec env (CocaseOfI _ _ _ t tmcasesI) = do 
  termLocallyClosedRec env t
  sequence_ (termCaseILocallyClosedRec env <$> tmcasesI)


termLocallyClosed :: Term pc -> Either Error ()
termLocallyClosed = termLocallyClosedRec []

---------------------------------------------------------------------------------
-- Shifting
--
-- Used in program transformations like focusing.
---------------------------------------------------------------------------------

shiftPCTermRec :: Int -> PrdCnsTerm -> PrdCnsTerm
shiftPCTermRec n (PrdTerm tm) = PrdTerm $ shiftTermRec n tm
shiftPCTermRec n (CnsTerm tm) = CnsTerm $ shiftTermRec n tm

shiftTermRec :: Int -> Term pc -> Term pc
shiftTermRec _ var@FreeVar {} = var
shiftTermRec n (BoundVar loc pcrep annot (i,j)) | n <= i    = BoundVar loc pcrep annot (i + 1, j)
                                                | otherwise = BoundVar loc pcrep annot (i    , j)
shiftTermRec n (Xtor loc pcrep annot ns xt subst) =
    Xtor loc pcrep annot ns xt (shiftPCTermRec n <$> subst)
shiftTermRec n (XCase loc pcrep annot ns cases) =
  XCase loc pcrep annot ns (shiftCmdCaseRec (n + 1) <$> cases)
shiftTermRec n (MuAbs loc pcrep annot bs cmd) =
  MuAbs loc pcrep annot bs (shiftCmdRec (n + 1) cmd)
shiftTermRec n (Dtor loc pcrep annot ns xt e (args1,pcrep',args2)) =
  Dtor loc pcrep annot ns xt (shiftTermRec n e) (shiftPCTermRec n <$> args1,pcrep',shiftPCTermRec n <$> args2)
shiftTermRec n (CaseOf loc pcrep annot ns e cases) =
  CaseOf loc pcrep annot ns (shiftTermRec n e) (shiftTermCaseRec (n + 1) <$> cases)
shiftTermRec n (CocaseI loc pcrep annot ns cases) =
  CocaseI loc pcrep annot ns (shiftTermCaseIRec n <$> cases)
shiftTermRec n (CaseI loc pcrep annot ns tmcasesI) =
  CaseI loc pcrep annot ns (shiftTermCaseIRec (n + 1) <$> tmcasesI)
shiftTermRec n (Semi loc rep annot ns xt (args1,pcrep',args2) t) =
  Semi loc rep annot ns xt (shiftPCTermRec n <$> args1,pcrep',shiftPCTermRec n <$> args2) (shiftTermRec n t)
shiftTermRec n (CocaseOf loc rep annot ns t tmcases) =
  CocaseOf loc rep annot ns (shiftTermRec n t) (shiftTermCaseRec (n + 1) <$> tmcases) 
shiftTermRec _ lit@PrimLitI64{} = lit
shiftTermRec _ lit@PrimLitF64{} = lit

shiftTermCaseRec :: Int -> TermCase pc -> TermCase pc
shiftTermCaseRec n (MkTermCase ext xt args e) = MkTermCase ext xt args (shiftTermRec n e)

shiftTermCaseIRec :: Int -> TermCaseI pc -> TermCaseI pc
shiftTermCaseIRec n (MkTermCaseI ext xt args e) = MkTermCaseI ext xt args (shiftTermRec n e)

shiftCmdCaseRec :: Int -> CmdCase -> CmdCase
shiftCmdCaseRec n (MkCmdCase ext name bs cmd) = MkCmdCase ext name bs (shiftCmdRec n cmd)

shiftCmdRec :: Int -> Command -> Command
shiftCmdRec n (Apply ext kind prd cns) =
  Apply ext kind (shiftTermRec n prd) (shiftTermRec n cns)
shiftCmdRec _ (ExitSuccess ext) =
  ExitSuccess ext
shiftCmdRec _ (ExitFailure ext) =
  ExitFailure ext
shiftCmdRec n (Print ext prd cmd) =
  Print ext (shiftTermRec n prd) (shiftCmdRec n cmd)
shiftCmdRec n (Read ext cns) =
  Read ext (shiftTermRec n cns)
shiftCmdRec _ (Jump ext fv) =
  Jump ext fv
shiftCmdRec n (PrimOp ext pt op subst) =
  PrimOp ext pt op (shiftPCTermRec n <$> subst)
shiftCmdRec n (CaseOfCmd loc ns t cmdcases) =
  CaseOfCmd loc ns  (shiftTermRec n t) $ map (shiftCmdCaseRec n) cmdcases
shiftCmdRec n (CaseOfI loc pcrep ns t tmcasesI) =
  CaseOfI loc pcrep ns (shiftTermRec n t) $ map (shiftTermCaseIRec n) tmcasesI
shiftCmdRec n (CocaseOfCmd loc ns t cmdcases) =
  CocaseOfCmd loc ns (shiftTermRec n t) $ map (shiftCmdCaseRec n) cmdcases
shiftCmdRec n (CocaseOfI loc pcrep ns t tmcasesI) =
  CocaseOfI loc pcrep ns (shiftTermRec n t) $ map (shiftTermCaseIRec n) tmcasesI

-- | Shift all unbound BoundVars up by one.
shiftCmd :: Command -> Command
shiftCmd = shiftCmdRec 0

