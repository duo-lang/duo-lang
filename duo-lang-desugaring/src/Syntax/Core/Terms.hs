module Syntax.Core.Terms
  ( -- Terms
    Term(..)
  , PrdCnsTerm(..)
  , Substitution(..)
  , CmdCase(..)
  , InstanceCase(..)
  , Command(..)
  , Pattern(..)
  -- Functions
  , termLocallyClosed
  ) where

import Data.List (elemIndex)
import Data.Maybe (fromJust, isJust)
import Data.Text qualified as T
import Syntax.Core.Annot
import Loc
import Errors.Desugarer
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.RST.Terms qualified as RST
import Syntax.RST.Types
import Syntax.CST.Names
    ( ClassName, FreeVarName, MethodName, XtorName )
import Syntax.LocallyNameless (LocallyNameless (..), Index, Shiftable (..), ShiftDirection(..))
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

--deriving instance Eq PrdCnsTerm 
deriving instance Show PrdCnsTerm

newtype Substitution = MkSubstitution { unSubstitution :: [PrdCnsTerm] }
  deriving (Show)

instance NMap Substitution PrdCnsTerm where
  nmap f = MkSubstitution . fmap f . (\x -> x.unSubstitution)
  nmapM f = fmap MkSubstitution . mapM f . (\x -> x.unSubstitution)

data Pattern where
  XtorPat :: Loc -> XtorName -> [(PrdCns, Maybe FreeVarName)] -> Pattern

deriving instance Show Pattern

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

--deriving instance Eq CmdCase
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
  , instancecase_pat :: Pattern
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
  -- | A bound variable in the locally nameless system.
  BoundVar :: Loc -> PrdCnsRep pc -> Index -> Term pc
  -- | A free variable in the locally nameless system.
  FreeVar :: Loc -> PrdCnsRep pc -> FreeVarName -> Term pc
  -- | A constructor or destructor.
  -- If the first argument is `PrdRep` it is a constructor, a destructor otherwise.
  Xtor :: Loc -> XtorAnnot -> PrdCnsRep pc -> RST.NominalStructural -> XtorName -> Substitution -> Term pc
  -- | A pattern or copattern match.
  -- If the first argument is `PrdRep` it is a copattern match, a pattern match otherwise.
  XCase :: Loc -> MatchAnnot pc' -> PrdCnsRep pc -> RST.NominalStructural -> [CmdCase] -> Term pc
  -- | A Mu or TildeMu abstraction:
  --
  --  mu k.c    =   MuAbs PrdRep c
  -- ~mu x.c    =   MuAbs CnsRep c
  MuAbs :: Loc -> MuAnnot -> PrdCnsRep pc -> Maybe FreeVarName -> Command -> Term pc
  -- | Primitive literals
  PrimLitI64 :: Loc -> Integer -> Term Prd
  PrimLitF64 :: Loc -> Double -> Term Prd
  PrimLitChar :: Loc -> Char -> Term Prd
  PrimLitString :: Loc -> String -> Term Prd
--deriving instance Eq (Term Prd)
--deriving instance Eq (Term Cns)
deriving instance Show (Term Prd)
deriving instance Show (Term Cns)

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------


-- | An executable command.
data Command where
  -- | A producer applied to a consumer:
  --
  --   p >> c
  Apply  :: Loc -> ApplyAnnot -> Term Prd -> Term Cns -> Command
  Print  :: Loc -> Term Prd -> Command -> Command
  Read   :: Loc -> Term Cns -> Command
  Jump   :: Loc -> FreeVarName -> Command
  Method :: Loc -> MethodName -> ClassName -> Maybe (Typ Pos, Typ Neg) -> Substitution -> Command
  ExitSuccess :: Loc -> Command
  ExitFailure :: Loc -> Command
  PrimOp :: Loc -> RST.PrimitiveOp -> Substitution -> Command

--deriving instance Eq Command
deriving instance Show Command


---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

pctermOpeningRec :: Int -> Substitution -> PrdCnsTerm -> PrdCnsTerm
pctermOpeningRec k subst (PrdTerm tm) = PrdTerm $ termOpeningRec k subst tm
pctermOpeningRec k subst (CnsTerm tm) = CnsTerm $ termOpeningRec k subst tm

termOpeningRec :: Int -> Substitution -> Term pc -> Term pc
termOpeningRec k subst bv@(BoundVar _ pcrep(i,j)) | i == k    = case (pcrep, subst.unSubstitution !! j) of
                                                                     (PrdRep, PrdTerm tm) -> tm
                                                                     (CnsRep, CnsTerm tm) -> tm
                                                                     _                    -> error "termOpeningRec BOOM"
                                                  | otherwise = bv
termOpeningRec _ _ fv@FreeVar{} = fv
termOpeningRec k args (Xtor loc annot rep ns xt subst) =
  Xtor loc annot rep ns xt (pctermOpeningRec k args <¢> subst)
termOpeningRec k args (XCase loc annot rep ns cases) =
  XCase loc annot rep ns $ map (\pmcase -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args pmcase.cmdcase_cmd }) cases
termOpeningRec k args (MuAbs loc annot rep fv cmd) =
  MuAbs loc annot rep fv (commandOpeningRec (k+1) args cmd)
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
commandOpeningRec k args (Apply loc annot t1 t2) =
  Apply loc annot (termOpeningRec k args t1) (termOpeningRec k args t2)
commandOpeningRec k args (PrimOp loc op subst) =
  PrimOp loc op (pctermOpeningRec k args <¢> subst)

---------------------------------------------------------------------------------
-- Variable Closing
---------------------------------------------------------------------------------

pctermClosingRec :: Int -> [(PrdCns, FreeVarName)] -> PrdCnsTerm -> PrdCnsTerm
pctermClosingRec k vars (PrdTerm tm) = PrdTerm $ termClosingRec k vars tm
pctermClosingRec k vars (CnsTerm tm) = CnsTerm $ termClosingRec k vars tm

termClosingRec :: Int -> [(PrdCns, FreeVarName)] -> Term pc -> Term pc
termClosingRec _ _ bv@BoundVar{} = bv
termClosingRec k vars (FreeVar loc PrdRep v) | isJust ((Prd,v) `elemIndex` vars) = BoundVar loc PrdRep (k, fromJust ((Prd,v) `elemIndex` vars))
                                             | otherwise = FreeVar loc PrdRep v
termClosingRec k vars (FreeVar loc CnsRep v) | isJust ((Cns,v) `elemIndex` vars) = BoundVar loc CnsRep (k, fromJust ((Cns,v) `elemIndex` vars))
                                             | otherwise = FreeVar loc CnsRep v
termClosingRec k vars (Xtor loc annot pc ns xt subst) =
  Xtor loc annot pc ns xt (pctermClosingRec k vars <¢> subst)
termClosingRec k vars (XCase loc annot pc sn cases) =
  XCase loc annot pc sn $ map (\pmcase -> pmcase { cmdcase_cmd = commandClosingRec (k+1) vars pmcase.cmdcase_cmd }) cases
termClosingRec k vars (MuAbs loc annot pc fv cmd) =
  MuAbs loc annot pc fv (commandClosingRec (k+1) vars cmd)
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
commandClosingRec k args (Method loc mn cn ty subst) =
  Method loc mn cn ty (pctermClosingRec k args <¢> subst)
commandClosingRec k args (Print ext t cmd) =
  Print ext (termClosingRec k args t) (commandClosingRec k args cmd)
commandClosingRec k args (Read ext cns) =
  Read ext (termClosingRec k args cns)
commandClosingRec k args (Apply ext annot t1 t2) =
  Apply ext annot (termClosingRec k args t1) (termClosingRec k args t2)
commandClosingRec k args (PrimOp ext op subst) =
  PrimOp ext op (pctermClosingRec k args <¢> subst)

instance LocallyNameless Substitution [(PrdCns, FreeVarName)] Command where
  openRec  = commandOpeningRec
  closeRec = commandClosingRec

instance LocallyNameless Substitution [(PrdCns, FreeVarName)] (Term pc) where
  openRec  = termOpeningRec
  closeRec = termClosingRec

---------------------------------------------------------------------------------
-- Check for locally closedness
---------------------------------------------------------------------------------

checkIfBound :: [[(PrdCns,a)]] -> PrdCnsRep pc -> Index -> Either DesugaringError ()
checkIfBound env rep  (i, j) | i >= length env = Left $ UnknownDesugaringError defaultLoc $ "Variable " <> T.pack (show (i,j)) <> " is not bound (Outer index)"
                             | otherwise = checkIfBoundInner (env !! i) rep (i,j)

checkIfBoundInner :: [(PrdCns,a)] -> PrdCnsRep pc -> Index -> Either DesugaringError ()
checkIfBoundInner vars PrdRep idx@(_,j) =
  if j < length vars
    then case vars !! j of
      (Prd,_) -> return ()
      (Cns,_) -> Left $ UnknownDesugaringError defaultLoc $ "Variable " <> T.pack (show idx) <> " is not bound to Producer"
    else Left $ UnknownDesugaringError defaultLoc $ "Variable " <> T.pack (show idx) <> " is not bound (Inner index)"
checkIfBoundInner vars CnsRep idx@(_,j) =
  if j < length vars
    then case vars !! j of
      (Cns,_) -> return ()
      (Prd,_) -> Left $ UnknownDesugaringError defaultLoc $ "Variable " <> T.pack (show idx) <> " is not bound to Consumer"
    else Left $ UnknownDesugaringError defaultLoc $ "Variable " <> T.pack (show idx) <> " is not bound (Inner index)"

pctermLocallyClosedRec :: [[(PrdCns, ())]] -> PrdCnsTerm -> Either DesugaringError ()
pctermLocallyClosedRec env (PrdTerm tm) = termLocallyClosedRec env tm
pctermLocallyClosedRec env (CnsTerm tm) = termLocallyClosedRec env tm

termLocallyClosedRec :: [[(PrdCns,())]] -> Term pc -> Either DesugaringError ()
termLocallyClosedRec env (BoundVar _ pc idx) = checkIfBound env pc idx
termLocallyClosedRec _ FreeVar{} = Right ()
termLocallyClosedRec env (Xtor _ _ _ _ _ subst) = do
  mapM_ (pctermLocallyClosedRec env) (subst.unSubstitution)
termLocallyClosedRec env (XCase _ _ _ _ cases) = do
  let f cmdcase  = case cmdcase.cmdcase_pat of
                         XtorPat _ _ args -> commandLocallyClosedRec (((\(x,_) -> (x,())) <$> args) : env) cmdcase.cmdcase_cmd
  mapM_ f cases
termLocallyClosedRec env (MuAbs _ _ PrdRep _ cmd) = commandLocallyClosedRec ([(Cns,())] : env) cmd
termLocallyClosedRec env (MuAbs _ _ CnsRep _ cmd) = commandLocallyClosedRec ([(Prd,())] : env) cmd
termLocallyClosedRec _ (PrimLitI64 _ _) = Right ()
termLocallyClosedRec _ (PrimLitF64 _ _) = Right ()
termLocallyClosedRec _ (PrimLitChar _ _) = Right ()
termLocallyClosedRec _ (PrimLitString _ _) = Right ()

commandLocallyClosedRec :: [[(PrdCns,())]] -> Command -> Either DesugaringError ()
commandLocallyClosedRec _ (ExitSuccess _) = Right ()
commandLocallyClosedRec _ (ExitFailure _) = Right ()
commandLocallyClosedRec _ (Jump _ _) = Right ()
commandLocallyClosedRec env (Method _ _ _ _ subst) = mapM_ (pctermLocallyClosedRec env) (subst.unSubstitution)
commandLocallyClosedRec env (Print _ t cmd) = termLocallyClosedRec env t >> commandLocallyClosedRec env cmd
commandLocallyClosedRec env (Read _ cns) = termLocallyClosedRec env cns
commandLocallyClosedRec env (Apply _ _ t1 t2) = termLocallyClosedRec env t1 >> termLocallyClosedRec env t2
commandLocallyClosedRec env (PrimOp _ _ subst) = mapM_ (pctermLocallyClosedRec env) (subst.unSubstitution)

termLocallyClosed :: Term pc -> Either DesugaringError ()
termLocallyClosed = termLocallyClosedRec []

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
  -- If (n <= i), then the bound variable was free from the position where shift was called.
  shiftRec ShiftUp n (BoundVar loc pcrep (i,j)) | n <= i    = BoundVar loc pcrep (i + 1, j)
                                                | otherwise = BoundVar loc pcrep (i    , j)
  shiftRec ShiftDown n (BoundVar loc pcrep (i,j)) | n <= i    = BoundVar loc pcrep (i - 1, j)
                                                  | otherwise = BoundVar loc pcrep (i    , j)
  shiftRec _ _ var@FreeVar {} = var
  shiftRec dir n (Xtor loc annot pcrep ns xt subst) =
    Xtor loc annot pcrep ns xt (shiftRec dir n <¢> subst)
  shiftRec dir n (XCase loc annot pcrep ns cases) =
    XCase loc annot pcrep ns (shiftRec dir (n + 1) <$> cases)
  shiftRec dir n (MuAbs loc annot pcrep bs cmd) =
    MuAbs loc annot pcrep bs (shiftRec dir (n + 1) cmd)
  shiftRec _ _ lit@PrimLitI64{} = lit
  shiftRec _ _ lit@PrimLitF64{} = lit
  shiftRec _ _ lit@PrimLitChar{} = lit
  shiftRec _ _ lit@PrimLitString{} = lit

instance Shiftable CmdCase where
  shiftRec :: ShiftDirection -> Int -> CmdCase -> CmdCase
  shiftRec dir n (MkCmdCase ext pat cmd) = MkCmdCase ext pat (shiftRec dir n cmd)

instance Shiftable Command where
  shiftRec :: ShiftDirection -> Int -> Command -> Command
  shiftRec dir n (Apply loc annot prd cns) = Apply loc annot (shiftRec dir n prd) (shiftRec dir n cns)
  shiftRec _ _ (ExitSuccess ext) = ExitSuccess ext
  shiftRec _ _ (ExitFailure ext) = ExitFailure ext
  shiftRec dir n (Print ext prd cmd) = Print ext (shiftRec dir n prd) (shiftRec dir n cmd)
  shiftRec dir n (Read ext cns) = Read ext (shiftRec dir n cns)
  shiftRec _ _ (Jump ext fv) = Jump ext fv
  shiftRec dir n (Method ext mn cn ty subst) = Method ext mn cn ty (shiftRec dir n <¢> subst)
  shiftRec dir n (PrimOp ext op subst) = PrimOp ext op (shiftRec dir n <¢> subst)
