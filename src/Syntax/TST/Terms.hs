module Syntax.TST.Terms
  ( -- Terms
    Term(..)
  , PrdCnsTerm(..)
  , Substitution(..)
  , CmdCase(..)
  , InstanceCase(..)
  , Command(..)
  , InstanceResolved(..)
  -- Functions
  , ShiftDirection(..)
  , getTypeTerm
  , getTypArgs
  , termLocallyClosed
  , instanceCaseLocallyClosed
  ) where

import Data.List (elemIndex)
import Data.Maybe (fromJust, isJust)
import Data.Text qualified as T

import Loc
import Errors
import Syntax.CST.Names
    ( ClassName, FreeVarName, MethodName, XtorName )
import Syntax.Core.Annot
    ( ApplyAnnot, MatchAnnot, MuAnnot, XtorAnnot )
import Syntax.Core.Terms qualified as Core
import Syntax.RST.Kinds ( AnyKind )
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.RST.Terms qualified as RST
import Syntax.RST.Types (Polarity(..), PolarityRep(..))
import Syntax.RST.Names

import Syntax.RST.Program (PrdCnsToPol)
import Syntax.TST.Types
import Data.Bifunctor (Bifunctor(second))
import Syntax.LocallyNameless (LocallyNameless (..), Index, ShiftDirection(..), Shiftable (..))
import Syntax.NMap (NMap (..), (<¢>))

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

newtype Substitution = MkSubstitution { unSubstitution :: [PrdCnsTerm] }
  deriving (Show)

instance NMap Substitution PrdCnsTerm where
  nmap f = MkSubstitution . fmap f . (\x -> x.unSubstitution)
  nmapM f = fmap MkSubstitution . mapM f . (\x -> x.unSubstitution)


-- | Represents one case in a pattern match or copattern match.
--
--        X Gamma           => c
--        ^ ^^^^^-----         ^------
--        |          |               |
--    cmdcase_name  cmdcase_args      cmdcase_cmd
--
data CmdCase = MkCmdCase
  { cmdcase_loc  :: Loc
  , cmdcase_pat :: Core.Pattern
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
  , instancecase_pat :: Core.Pattern
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
  Xtor :: Loc -> XtorAnnot -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> RST.NominalStructural -> XtorName -> Substitution -> Term pc
  -- | A pattern or copattern match.
  -- If the first argument is `PrdRep` it is a copattern match, a pattern match otherwise.
  XCase :: Loc -> MatchAnnot pc' -> PrdCnsRep pc -> Typ (PrdCnsToPol pc) -> RST.NominalStructural -> [CmdCase] -> Term pc
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
    Xtor loc annot rep (zonk vt bisubst ty) ns xt (zonk vt bisubst <¢> subst)
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
getTypArgs subst = getTypArgs'' <$> subst.unSubstitution
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
  Apply  :: Loc -> ApplyAnnot -> AnyKind -> Term Prd -> Term Cns -> Command
  Print  :: Loc -> Term Prd -> Command -> Command
  Read   :: Loc -> Term Cns -> Command
  Jump   :: Loc -> FreeVarName -> Command
  Method :: Loc -> MethodName -> ClassName -> InstanceResolved -> Maybe (Typ Pos, Typ Neg) -> Substitution -> Command
  ExitSuccess :: Loc -> Command
  ExitFailure :: Loc -> Command
  PrimOp :: Loc -> RST.PrimitiveOp -> Substitution -> Command

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
  zonk vt bisubst (Method ext mn cn inst ty subst) =
    Method ext mn cn inst ty (zonk vt bisubst <¢> subst)
  zonk _vt _ (ExitSuccess ext) =
    ExitSuccess ext
  zonk _vt _ (ExitFailure ext) =
    ExitFailure ext
  zonk vt bisubst (PrimOp ext op subst) =
    PrimOp ext op (zonk vt bisubst <¢> subst)

data InstanceResolved where
  InstanceResolved :: FreeVarName -> InstanceResolved
  InstanceUnresolved :: UniTVar -> InstanceResolved
deriving instance Show InstanceResolved

---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

pctermOpeningRec :: Int -> Substitution -> PrdCnsTerm -> PrdCnsTerm
pctermOpeningRec k subst (PrdTerm tm) = PrdTerm $ termOpeningRec k subst tm
pctermOpeningRec k subst (CnsTerm tm) = CnsTerm $ termOpeningRec k subst tm


termOpeningRec :: Int -> Substitution -> Term pc -> Term pc
-- Core constructs
termOpeningRec k subst bv@(BoundVar _ pcrep _ (i,j)) | i == k    = case (pcrep, subst.unSubstitution !! j) of
                                                                      (PrdRep, PrdTerm tm) -> tm
                                                                      (CnsRep, CnsTerm tm) -> tm
                                                                      _                    -> error "termOpeningRec BOOM"
                                                   | otherwise = bv
termOpeningRec _ _ fv@FreeVar {} = fv
termOpeningRec k args (Xtor loc annot rep ty ns xt subst) =
  Xtor loc annot rep ty ns xt (pctermOpeningRec k args <¢> subst)
termOpeningRec k args (XCase loc annot rep ty ns cases) =
  XCase loc annot rep ty ns $ map (\pmcase -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args pmcase.cmdcase_cmd }) cases
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
commandOpeningRec k args (Method loc mn cn inst ty subst) =
  Method loc mn cn inst ty (pctermOpeningRec k args <¢> subst)
commandOpeningRec k args (Apply loc annot kind t1 t2) =
  Apply loc annot kind (termOpeningRec k args t1) (termOpeningRec k args t2)
commandOpeningRec k args (PrimOp loc op subst) =
  PrimOp loc op (pctermOpeningRec k args <¢> subst)

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
  Xtor loc ty pc annot ns xt (pctermClosingRec k vars <¢> subst)
termClosingRec k vars (XCase loc annot pc ty sn cases) =
  XCase loc annot pc ty sn $ map (\pmcase -> pmcase { cmdcase_cmd = commandClosingRec (k+1) vars pmcase.cmdcase_cmd }) cases
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
commandClosingRec k args (Method ext mn cn inst ty subst) =
  Method ext mn cn inst ty (pctermClosingRec k args <¢> subst)
commandClosingRec k args (Apply ext annot kind t1 t2) =
  Apply ext annot kind (termClosingRec k args t1) (termClosingRec k args t2)
commandClosingRec k args (PrimOp ext op subst) =
  PrimOp ext op (pctermClosingRec k args <¢> subst)

instance LocallyNameless Substitution [(PrdCns, FreeVarName)] Command where
  openRec  = commandOpeningRec
  closeRec = commandClosingRec

instance LocallyNameless Substitution [(PrdCns, FreeVarName)] (Term pc) where
  openRec  = termOpeningRec
  closeRec = termClosingRec

instance LocallyNameless Substitution [(PrdCns, FreeVarName)] PrdCnsTerm where
  openRec  = pctermOpeningRec
  closeRec = pctermClosingRec

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
  sequence_ (pctermLocallyClosedRec env <$> subst.unSubstitution)
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
cmdCaseLocallyClosedRec env (MkCmdCase _ (Core.XtorPat _ _ args) cmd)= do
  commandLocallyClosedRec (((\(x,_) -> (x,())) <$> args):env) cmd

commandLocallyClosedRec :: [[(PrdCns,())]] -> Command -> Either Error ()
commandLocallyClosedRec _ (ExitSuccess _) = Right ()
commandLocallyClosedRec _ (ExitFailure _) = Right ()
commandLocallyClosedRec _ (Jump _ _) = Right ()
commandLocallyClosedRec env (Print _ t cmd) = termLocallyClosedRec env t >> commandLocallyClosedRec env cmd
commandLocallyClosedRec env (Read _ cns) = termLocallyClosedRec env cns
commandLocallyClosedRec env (Apply _ _ _ t1 t2) = termLocallyClosedRec env t1 >> termLocallyClosedRec env t2
commandLocallyClosedRec env (Method _ _ _ _ _ subst) = sequence_ $ pctermLocallyClosedRec env <$> subst.unSubstitution
commandLocallyClosedRec env (PrimOp _ _ subst) = sequence_ $ pctermLocallyClosedRec env <$> subst.unSubstitution

termLocallyClosed :: Term pc -> Either Error ()
termLocallyClosed = termLocallyClosedRec []

instanceCaseLocallyClosed :: InstanceCase -> Either Error ()
instanceCaseLocallyClosed (MkInstanceCase _ (Core.XtorPat _ _ args) cmd) =
  commandLocallyClosedRec [second (const ()) <$> args] cmd

---------------------------------------------------------------------------------
-- Shifting
--
-- Used in program transformations like focusing.
---------------------------------------------------------------------------------

instance Shiftable PrdCnsTerm where
  shiftRec :: ShiftDirection -> Int -> PrdCnsTerm -> PrdCnsTerm
  shiftRec dir n (PrdTerm tm) = PrdTerm $ shiftRec dir n tm
  shiftRec dir n (CnsTerm tm) = CnsTerm $ shiftRec dir n tm

instance Shiftable (Term pc) where
  shiftRec :: ShiftDirection -> Int -> Term pc -> Term pc
  -- Core constructs
  shiftRec _ _ var@FreeVar {} = var
  shiftRec ShiftUp n (BoundVar loc pcrep ty (i,j)) | n <= i    = BoundVar loc pcrep ty (i + 1, j)
                                                   | otherwise = BoundVar loc pcrep ty (i    , j)
  shiftRec ShiftDown n (BoundVar loc pcrep ty (i,j)) | n <= i    = BoundVar loc pcrep ty (i - 1, j)
                                                     | otherwise = BoundVar loc pcrep ty (i    , j)
  shiftRec dir n (Xtor loc annot pcrep ty ns xt subst) =
    Xtor loc annot pcrep ty ns xt (shiftRec dir n <¢> subst)
  shiftRec dir n (XCase loc annot pcrep ty ns cases) =
    XCase loc annot pcrep ty ns (shiftRec dir (n + 1) <$> cases)
  shiftRec dir n (MuAbs loc annot pcrep ty bs cmd) =
    MuAbs loc annot pcrep ty bs (shiftRec dir (n + 1) cmd)
  -- Primitive constructs
  shiftRec _ _ lit@PrimLitI64{} = lit
  shiftRec _ _ lit@PrimLitF64{} = lit
  shiftRec _ _ lit@PrimLitChar{} = lit
  shiftRec _ _ lit@PrimLitString{} = lit

instance Shiftable CmdCase where
  shiftRec :: ShiftDirection -> Int -> CmdCase -> CmdCase
  shiftRec dir n pmcase =
    MkCmdCase { cmdcase_loc = pmcase.cmdcase_loc
              , cmdcase_pat = pmcase.cmdcase_pat
              , cmdcase_cmd = shiftRec dir n pmcase.cmdcase_cmd
              }

instance Shiftable Command where
  shiftRec :: ShiftDirection -> Int -> Command -> Command
  shiftRec dir n (Apply ext annot kind prd cns) =
    Apply ext annot kind (shiftRec dir n prd) (shiftRec dir n cns)
  shiftRec _ _ (ExitSuccess ext) =
    ExitSuccess ext
  shiftRec _ _ (ExitFailure ext) =
    ExitFailure ext
  shiftRec dir n (Print ext prd cmd) =
    Print ext (shiftRec dir n prd) (shiftRec dir n cmd)
  shiftRec dir n (Read ext cns) =
    Read ext (shiftRec dir n cns)
  shiftRec _ _ (Jump ext fv) =
    Jump ext fv
  shiftRec dir n (Method ext mn cn inst ty subst) =
    Method ext mn cn inst ty (shiftRec dir n <¢> subst)
  shiftRec dir n (PrimOp ext op subst) =
    PrimOp ext op (shiftRec dir n <¢> subst)
