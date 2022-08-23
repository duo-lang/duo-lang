module Syntax.TST.Terms
  ( -- Terms
    Term(..)
  , PrdCnsTerm(..)
  , Substitution
  , RST.Pattern(..)
  , CmdCase(..)
  , InstanceCase(..)
  , Command(..)
  -- Functions
  , commandClosing
  , ShiftDirection(..)
  , shiftCmd
  , getTypeTerm
  , getTypArgs
  , commandOpening
  , termLocallyClosed
  , instanceCaseLocallyClosed
  ) where

import Data.List (elemIndex)
import Data.Maybe (fromJust, isJust)
import Data.Text qualified as T

import Utils
import Errors
import Syntax.CST.Names
    ( ClassName, FreeVarName, Index, MethodName, XtorName )
import Syntax.Core.Annot
    ( ApplyAnnot, MatchAnnot, MuAnnot, XtorAnnot )
import Syntax.CST.Kinds ( MonoKind )
import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.RST.Terms qualified as RST
import Syntax.RST.Types (Polarity(..), PolarityRep(..))
import Syntax.RST.Program (PrdCnsToPol)
import Syntax.TST.Types
import Data.Bifunctor (Bifunctor(second))

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

instance Zonk PrdCnsTerm where
  zonk vt bisubst (PrdTerm tm) = PrdTerm (zonk vt bisubst tm)
  zonk vt bisubst (CnsTerm tm) = CnsTerm (zonk vt bisubst tm)

type Substitution = [PrdCnsTerm]


-- | Represents one case in a pattern match or copattern match.
--
--        X Gamma           => c
--        ^ ^^^^^-----         ^------
--        |          |               |
--    cmdcase_name  cmdcase_args      cmdcase_cmd
--
data CmdCase = MkCmdCase
  { cmdcase_loc  :: Loc
  , cmdcase_pat :: RST.Pattern
  , cmdcase_cmd  :: Command
  }

instance Zonk CmdCase where
  zonk vt bisubst (MkCmdCase loc pat cmd) =
    MkCmdCase loc pat (zonk vt bisubst cmd)

deriving instance Show CmdCase


-- | Represents the implementation of a type class method.
--
--        Gamma           => c
--        ^^^^^-----         ^------
--              |               |
--      instancecase_args   instancecase_cmd
--
data InstanceCase = MkInstanceCase
  { instancecase_loc :: Loc
  , instancecase_pat :: RST.Pattern
  , instancecase_cmd :: Command
  }

--deriving instance Eq CmdCase
deriving instance Show InstanceCase

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
  Xtor :: Loc -> XtorAnnot -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> CST.NominalStructural -> XtorName -> Substitution -> Term pc
  -- | A pattern or copattern match.
  -- If the first argument is `PrdRep` it is a copattern match, a pattern match otherwise.
  XCase :: Loc -> MatchAnnot pc' -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> CST.NominalStructural -> [CmdCase] -> Term pc
  -- | A Mu or TildeMu abstraction:
  --
  --  mu k.c    =   MuAbs PrdRep c
  -- ~mu x.c    =   MuAbs CnsRep c
  MuAbs :: Loc -> MuAnnot -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> Maybe FreeVarName -> Command -> Term pc
  ---------------------------------------------------------------------------------
  -- Primitive constructs
  ---------------------------------------------------------------------------------
  PrimLitI64 :: Loc -> Integer -> Term Prd
  PrimLitF64 :: Loc -> Double -> Term Prd
  PrimLitChar :: Loc -> Char -> Term Prd
  PrimLitString :: Loc -> String -> Term Prd

deriving instance Show (Term pc)

instance Zonk (Term pc) where
  -- Core constructs
  zonk vt bisubst (BoundVar loc rep ty idx) =
    BoundVar loc rep (zonk vt bisubst ty) idx
  zonk vt bisubst (FreeVar loc rep ty nm)  =
    FreeVar loc rep (zonk vt bisubst ty) nm
  zonk vt bisubst (Xtor loc annot rep ty ns xt subst) =
    Xtor loc annot rep (zonk vt bisubst ty) ns xt (zonk vt bisubst <$> subst)
  zonk vt bisubst (XCase loc annot rep ty ns cases) =
    XCase loc annot rep (zonk vt bisubst ty) ns (zonk vt bisubst <$> cases)
  zonk vt bisubst (MuAbs loc annot rep ty fv cmd) =
    MuAbs loc annot rep (zonk vt bisubst ty) fv (zonk vt bisubst cmd)
  -- Primitive constructs  
  zonk _vt _ lit@PrimLitI64{} = lit
  zonk _vt _ lit@PrimLitF64{} = lit
  zonk _vt _ lit@PrimLitChar{} = lit
  zonk _vt _ lit@PrimLitString{} = lit

getTypeTerm :: forall pc. Term pc -> Typ (PrdCnsToPol pc)
-- Core constructs
getTypeTerm (BoundVar _ _ ty _) = ty
getTypeTerm (FreeVar  _ _ ty _) = ty
getTypeTerm (Xtor _ _ _ ty _ _ _) = ty
getTypeTerm (XCase _ _ _ ty _ _)  = ty
getTypeTerm (MuAbs _ _ _ ty _ _)  = ty
-- Primitive constructs
getTypeTerm (PrimLitI64 _ _) = TyI64 defaultLoc PosRep
getTypeTerm (PrimLitF64 _ _) = TyF64 defaultLoc PosRep
getTypeTerm (PrimLitChar _ _) = TyChar defaultLoc PosRep
getTypeTerm (PrimLitString _ _) = TyString defaultLoc PosRep

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
  Apply  :: Loc -> ApplyAnnot -> Maybe MonoKind -> Term Prd -> Term Cns -> Command
  Print  :: Loc -> Term Prd -> Command -> Command
  Read   :: Loc -> Term Cns -> Command
  Jump   :: Loc -> FreeVarName -> Command
  Method :: Loc -> MethodName -> ClassName -> Substitution -> Command
  ExitSuccess :: Loc -> Command
  ExitFailure :: Loc -> Command
  PrimOp :: Loc -> CST.PrimitiveOp -> Substitution -> Command

deriving instance Show Command

instance Zonk Command where
  zonk vt bisubst (Apply ext annot kind prd cns) =
    Apply ext annot kind (zonk vt bisubst prd) (zonk vt bisubst cns)
  zonk vt bisubst (Print ext prd cmd) =
    Print ext (zonk vt bisubst prd) (zonk vt bisubst cmd)
  zonk vt bisubst (Read ext cns) =
    Read ext (zonk vt bisubst cns)
  zonk _vt _ (Jump ext fv) =
    Jump ext fv
  zonk vt bisubst (Method ext mn cn subst) =
    Method ext mn cn (zonk vt bisubst <$> subst)
  zonk _vt _ (ExitSuccess ext) =
    ExitSuccess ext
  zonk _vt _ (ExitFailure ext) =
    ExitFailure ext
  zonk vt bisubst (PrimOp ext op subst) =
    PrimOp ext op (zonk vt bisubst <$> subst)

---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

pctermOpeningRec :: Int -> Substitution -> PrdCnsTerm -> PrdCnsTerm
pctermOpeningRec k subst (PrdTerm tm) = PrdTerm $ termOpeningRec k subst tm
pctermOpeningRec k subst (CnsTerm tm) = CnsTerm $ termOpeningRec k subst tm


termOpeningRec :: Int -> Substitution -> Term pc -> Term pc
-- Core constructs
termOpeningRec k subst bv@(BoundVar _ pcrep _ (i,j)) | i == k    = case (pcrep, subst !! j) of
                                                                      (PrdRep, PrdTerm tm) -> tm
                                                                      (CnsRep, CnsTerm tm) -> tm
                                                                      _                    -> error "termOpeningRec BOOM"
                                                   | otherwise = bv
termOpeningRec _ _ fv@FreeVar {} = fv
termOpeningRec k args (Xtor loc annot rep ty ns xt subst) =
  Xtor loc annot rep ty ns xt (pctermOpeningRec k args <$> subst)
termOpeningRec k args (XCase loc annot rep ty ns cases) =
  XCase loc annot rep ty ns $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args cmdcase_cmd }) cases
termOpeningRec k args (MuAbs loc annot rep ty fv cmd) =
  MuAbs loc annot rep ty  fv (commandOpeningRec (k+1) args cmd)
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
  Method loc mn cn (pctermOpeningRec k args <$> subst)
commandOpeningRec k args (Apply loc annot kind t1 t2) =
  Apply loc annot kind (termOpeningRec k args t1) (termOpeningRec k args t2)
commandOpeningRec k args (PrimOp loc op subst) =
  PrimOp loc op (pctermOpeningRec k args <$> subst)

commandOpening :: Substitution -> Command -> Command
commandOpening = commandOpeningRec 0

---------------------------------------------------------------------------------
-- Variable Closing
---------------------------------------------------------------------------------

pctermClosingRec :: Int -> [(PrdCns, FreeVarName)] -> PrdCnsTerm -> PrdCnsTerm
pctermClosingRec k vars (PrdTerm tm) = PrdTerm $ termClosingRec k vars tm
pctermClosingRec k vars (CnsTerm tm) = CnsTerm $ termClosingRec k vars tm

termClosingRec :: Int -> [(PrdCns, FreeVarName)] -> Term pc -> Term pc
-- Core constructs
termClosingRec _ _ bv@BoundVar {} = bv
termClosingRec k vars (FreeVar loc PrdRep ty v) | isJust ((Prd,v) `elemIndex` vars) = BoundVar loc PrdRep ty (k, fromJust ((Prd,v) `elemIndex` vars))
                                                   | otherwise = FreeVar loc PrdRep ty v
termClosingRec k vars (FreeVar loc CnsRep ty v) | isJust ((Cns,v) `elemIndex` vars) = BoundVar loc CnsRep ty (k, fromJust ((Cns,v) `elemIndex` vars))
                                                   | otherwise = FreeVar loc CnsRep ty v
termClosingRec k vars (Xtor loc ty pc annot ns xt subst) =
  Xtor loc ty pc annot ns xt (pctermClosingRec k vars <$> subst)
termClosingRec k vars (XCase loc annot pc ty sn cases) =
  XCase loc annot pc ty sn $ map (\pmcase@MkCmdCase { cmdcase_cmd } -> pmcase { cmdcase_cmd = commandClosingRec (k+1) vars cmdcase_cmd }) cases
termClosingRec k vars (MuAbs loc annot pc ty fv cmd) =
  MuAbs loc annot pc ty fv (commandClosingRec (k+1) vars cmd)
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
commandClosingRec k args (Print ext t cmd) =
  Print ext (termClosingRec k args t) (commandClosingRec k args cmd)
commandClosingRec k args (Read ext cns) =
  Read ext (termClosingRec k args cns)
commandClosingRec k args (Method ext mn cn subst) =
  Method ext mn cn (pctermClosingRec k args <$> subst)
commandClosingRec k args (Apply ext annot kind t1 t2) =
  Apply ext annot kind (termClosingRec k args t1) (termClosingRec k args t2)
commandClosingRec k args (PrimOp ext op subst) =
  PrimOp ext op (pctermClosingRec k args <$> subst)

commandClosing :: [(PrdCns, FreeVarName)] -> Command -> Command
commandClosing = commandClosingRec 0

---------------------------------------------------------------------------------
-- Check for locally closedness
---------------------------------------------------------------------------------

checkIfBound :: [[(PrdCns,a)]] -> PrdCnsRep pc -> Index -> Either Error ()
checkIfBound env rep  (i, j) | i >= length env = Left $ ErrOther $ SomeOtherError defaultLoc $ "Variable " <> T.pack (show (i,j)) <> " is not bound (Outer index)"
                             | otherwise = checkIfBoundInner (env !! i) rep (i,j)

checkIfBoundInner :: [(PrdCns,a)] -> PrdCnsRep pc -> Index -> Either Error ()
checkIfBoundInner vars PrdRep idx@(_,j) =
  if j < length vars
    then case vars !! j of
      (Prd,_) -> return ()
      (Cns,_) -> Left $ ErrOther $ SomeOtherError defaultLoc $ "Variable " <> T.pack (show idx) <> " is not bound to Producer"
    else Left $ ErrOther $ SomeOtherError defaultLoc $ "Variable " <> T.pack (show idx) <> " is not bound (Inner index)"
checkIfBoundInner vars CnsRep idx@(_,j) =
  if j < length vars
    then case vars !! j of
      (Cns,_) -> return ()
      (Prd,_) -> Left $ ErrOther $ SomeOtherError defaultLoc $ "Variable " <> T.pack (show idx) <> " is not bound to Consumer"
    else Left $ ErrOther $ SomeOtherError defaultLoc $ "Variable " <> T.pack (show idx) <> " is not bound (Inner index)"

pctermLocallyClosedRec :: [[(PrdCns, ())]] -> PrdCnsTerm -> Either Error ()
pctermLocallyClosedRec env (PrdTerm tm) = termLocallyClosedRec env tm
pctermLocallyClosedRec env (CnsTerm tm) = termLocallyClosedRec env tm

termLocallyClosedRec :: [[(PrdCns,())]] -> Term pc -> Either Error ()
-- Core constructs
termLocallyClosedRec env (BoundVar _ pc _ idx) = checkIfBound env pc idx
termLocallyClosedRec _ FreeVar {} = Right ()
termLocallyClosedRec env (Xtor _ _  _ _ _ _ subst) = do
  sequence_ (pctermLocallyClosedRec env <$> subst)
termLocallyClosedRec env (XCase _ _ _ _ _ cases) = do
  sequence_ (cmdCaseLocallyClosedRec env <$> cases)
termLocallyClosedRec env (MuAbs _ _ PrdRep _ _ cmd) = commandLocallyClosedRec ([(Cns,())] : env) cmd
termLocallyClosedRec env (MuAbs _ _ CnsRep _ _ cmd) = commandLocallyClosedRec ([(Prd,())] : env) cmd
-- Primitive constructs  
termLocallyClosedRec _ (PrimLitI64 _ _) = Right ()
termLocallyClosedRec _ (PrimLitF64 _ _) = Right ()
termLocallyClosedRec _ (PrimLitChar _ _) = Right ()
termLocallyClosedRec _ (PrimLitString _ _) = Right ()


cmdCaseLocallyClosedRec :: [[(PrdCns,())]] -> CmdCase -> Either Error ()
cmdCaseLocallyClosedRec env (MkCmdCase _ (RST.XtorPat _ _ args) cmd)= do
  commandLocallyClosedRec (((\(x,_) -> (x,())) <$> args):env) cmd

commandLocallyClosedRec :: [[(PrdCns,())]] -> Command -> Either Error ()
commandLocallyClosedRec _ (ExitSuccess _) = Right ()
commandLocallyClosedRec _ (ExitFailure _) = Right ()
commandLocallyClosedRec _ (Jump _ _) = Right ()
commandLocallyClosedRec env (Print _ t cmd) = termLocallyClosedRec env t >> commandLocallyClosedRec env cmd
commandLocallyClosedRec env (Read _ cns) = termLocallyClosedRec env cns
commandLocallyClosedRec env (Apply _ _ _ t1 t2) = termLocallyClosedRec env t1 >> termLocallyClosedRec env t2
commandLocallyClosedRec env (Method _ _ _ subst) = sequence_ $ pctermLocallyClosedRec env <$> subst
commandLocallyClosedRec env (PrimOp _ _ subst) = sequence_ $ pctermLocallyClosedRec env <$> subst

termLocallyClosed :: Term pc -> Either Error ()
termLocallyClosed = termLocallyClosedRec []

instanceCaseLocallyClosed :: InstanceCase -> Either Error ()
instanceCaseLocallyClosed (MkInstanceCase _ (RST.XtorPat _ _ args) cmd) =
  commandLocallyClosedRec [second (const ()) <$> args] cmd

---------------------------------------------------------------------------------
-- Shifting
--
-- Used in program transformations like focusing.
---------------------------------------------------------------------------------

data ShiftDirection = ShiftUp | ShiftDown
  deriving (Show, Eq)

shiftPCTermRec :: ShiftDirection -> Int -> PrdCnsTerm -> PrdCnsTerm
shiftPCTermRec dir n (PrdTerm tm) = PrdTerm $ shiftTermRec dir n tm
shiftPCTermRec dir n (CnsTerm tm) = CnsTerm $ shiftTermRec dir n tm

shiftTermRec :: ShiftDirection -> Int -> Term pc -> Term pc
-- Core constructs
shiftTermRec _ _ var@FreeVar {} = var
shiftTermRec ShiftUp n (BoundVar loc pcrep ty (i,j)) | n <= i    = BoundVar loc pcrep ty (i + 1, j)
                                                        | otherwise = BoundVar loc pcrep ty (i    , j)
shiftTermRec ShiftDown n (BoundVar loc pcrep ty (i,j)) | n <= i    = BoundVar loc pcrep ty (i - 1, j)
                                                          | otherwise = BoundVar loc pcrep ty (i    , j)
shiftTermRec dir n (Xtor loc annot pcrep ty ns xt subst) =
    Xtor loc annot pcrep ty ns xt (shiftPCTermRec dir n <$> subst)
shiftTermRec dir n (XCase loc annot pcrep ty ns cases) =
  XCase loc annot pcrep ty ns (shiftCmdCaseRec dir (n + 1) <$> cases)
shiftTermRec dir n (MuAbs loc annot pcrep ty bs cmd) =
  MuAbs loc annot pcrep ty bs (shiftCmdRec dir (n + 1) cmd)
-- Primitive constructs
shiftTermRec _ _ lit@PrimLitI64{} = lit
shiftTermRec _ _ lit@PrimLitF64{} = lit
shiftTermRec _ _ lit@PrimLitChar{} = lit
shiftTermRec _ _ lit@PrimLitString{} = lit

shiftCmdCaseRec :: ShiftDirection -> Int -> CmdCase -> CmdCase
shiftCmdCaseRec dir n MkCmdCase { cmdcase_loc, cmdcase_pat, cmdcase_cmd } =
  MkCmdCase { cmdcase_loc = cmdcase_loc
            , cmdcase_pat = cmdcase_pat
            , cmdcase_cmd = shiftCmdRec dir n cmdcase_cmd
            }

shiftCmdRec :: ShiftDirection -> Int -> Command -> Command
shiftCmdRec dir n (Apply ext annot kind prd cns) =
  Apply ext annot kind (shiftTermRec dir n prd) (shiftTermRec dir n cns)
shiftCmdRec _ _ (ExitSuccess ext) =
  ExitSuccess ext
shiftCmdRec _ _ (ExitFailure ext) =
  ExitFailure ext
shiftCmdRec dir n (Print ext prd cmd) =
  Print ext (shiftTermRec dir n prd) (shiftCmdRec dir n cmd)
shiftCmdRec dir n (Read ext cns) =
  Read ext (shiftTermRec dir n cns)
shiftCmdRec _ _ (Jump ext fv) =
  Jump ext fv
shiftCmdRec dir n (Method ext mn cn subst) =
  Method ext mn cn (shiftPCTermRec dir n <$> subst)
shiftCmdRec dir n (PrimOp ext op subst) =
  PrimOp ext op (shiftPCTermRec dir n <$> subst)

-- | Shift all unbound BoundVars up by one.
shiftCmd :: ShiftDirection -> Command -> Command
shiftCmd dir = shiftCmdRec dir 0

