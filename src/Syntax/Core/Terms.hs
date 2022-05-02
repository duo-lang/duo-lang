module Syntax.Core.Terms
  ( -- Terms
    Term(..)
  , PrdCnsTerm(..)
  , Substitution
  , Pattern(..)
  , CmdCase(..)
  , Command(..)
  , MuAnnot(..)
  , MatchAnnot(..)
  , XtorAnnot(..)
  , ApplyAnnot(..)
  -- Functions
  , commandClosing
  , shiftCmd
  , commandOpening
  , termLocallyClosed
  ) where

import Data.List (elemIndex)
import Data.Maybe (fromJust, isJust)
import Data.Text qualified as T

import Utils
import Errors
import Syntax.Common
import Syntax.AST.Terms (ShiftDirection(..))

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

type Substitution = [PrdCnsTerm]

---------------------------------------------------------------------------------
-- Pattern/copattern match cases
---------------------------------------------------------------------------------

data Pattern where
  XtorPat :: Loc -> XtorName -> [(PrdCns, Maybe FreeVarName)] -> Pattern

deriving instance Eq Pattern
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

deriving instance Eq CmdCase
deriving instance Show CmdCase

---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

data MuAnnot where
  -- | User-written Mu abstraction
  MuAnnotOrig :: MuAnnot
  -- Semi/Dtor
  MuAnnotSemi :: MuAnnot
  MuAnnotDtor :: MuAnnot
  -- CaseOf / CocaseOf
  MuAnnotCaseOf :: MuAnnot
  MuAnnotCocaseOf :: MuAnnot
  deriving (Ord, Eq, Show)

data MatchAnnot where
  -- | User-written XCase abstraction
  MatchAnnotOrig :: MatchAnnot
  -- CaseOf / CocaseOf
  MatchAnnotCaseOf :: MatchAnnot
  MatchAnnotCocaseOf :: MatchAnnot
  -- CaseI / CocaseI
  MatchAnnotCaseI :: MatchAnnot
  MatchAnnotCocaseI :: MatchAnnot
  -- CaseOfI / CocaseOfI
  MatchAnnotCaseOfI :: MatchAnnot
  MatchAnnotCocaseOfI :: MatchAnnot
  -- CaseOfCmd / CocaseOfCmd
  MatchAnnotCaseOfCmd :: MatchAnnot
  MatchAnnotCocaseOfCmd :: MatchAnnot
  deriving (Ord, Eq, Show)

data XtorAnnot where
  -- | User-written XCase abstraction
  XtorAnnotOrig :: XtorAnnot
  -- Semi/Dtor
  XtorAnnotSemi :: XtorAnnot
  XtorAnnotDtor :: XtorAnnot
  deriving (Ord, Eq, Show)

-- | A symmetric term.
-- The `bs` parameter is used to store additional information at binding sites.
data Term (pc :: PrdCns) where
  -- | A bound variable in the locally nameless system.
  BoundVar :: Loc -> PrdCnsRep pc -> Index -> Term pc
  -- | A free variable in the locally nameless system.
  FreeVar :: Loc -> PrdCnsRep pc -> FreeVarName -> Term pc
  -- | A constructor or destructor.
  -- If the first argument is `PrdRep` it is a constructor, a destructor otherwise.
  Xtor :: Loc -> XtorAnnot -> PrdCnsRep pc -> NominalStructural -> XtorName -> Substitution -> Term pc
  -- | A pattern or copattern match.
  -- If the first argument is `PrdRep` it is a copattern match, a pattern match otherwise.
  XCase :: Loc -> MatchAnnot -> PrdCnsRep pc -> NominalStructural -> [CmdCase] -> Term pc
  -- | A Mu or TildeMu abstraction:
  --
  --  mu k.c    =   MuAbs PrdRep c
  -- ~mu x.c    =   MuAbs CnsRep c
  MuAbs :: Loc -> MuAnnot -> PrdCnsRep pc -> Maybe FreeVarName -> Command -> Term pc
  -- | Primitive literals
  PrimLitI64 :: Loc -> Integer -> Term Prd
  PrimLitF64 :: Loc -> Double -> Term Prd
deriving instance Eq (Term Prd)
deriving instance Eq (Term Cns)
deriving instance Show (Term Prd)
deriving instance Show (Term Cns)

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

data ApplyAnnot where
  -- User-written apply command
  ApplyAnnotOrig :: ApplyAnnot
  -- Semi/Dtor
  ApplyAnnotSemi :: ApplyAnnot
  ApplyAnnotDtor :: ApplyAnnot
  -- CaseOf/CocaseOf
  ApplyAnnotCaseOfInner :: ApplyAnnot
  ApplyAnnotCaseOfOuter :: ApplyAnnot
  ApplyAnnotCocaseOfInner :: ApplyAnnot
  ApplyAnnotCocaseOfOuter :: ApplyAnnot
  -- CaseI/CocaseI
  ApplyAnnotCaseI :: ApplyAnnot
  ApplyAnnotCocaseI :: ApplyAnnot
  -- CaseOfCmd/CocaseOfCmd
  ApplyAnnotCaseOfCmd :: ApplyAnnot
  ApplyAnnotCocaseOfCmd :: ApplyAnnot
  -- CaseOfI/CocaseOfI
  ApplyAnnotCaseOfIInner :: Int -> ApplyAnnot
  ApplyAnnotCaseOfIOuter :: ApplyAnnot
  ApplyAnnotCocaseOfIInner :: Int -> ApplyAnnot
  ApplyAnnotCocaseOfIOuter :: ApplyAnnot
  deriving (Ord, Eq, Show)

-- | An executable command.
data Command where
  -- | A producer applied to a consumer:
  --
  --   p >> c
  Apply  :: Loc -> ApplyAnnot -> Maybe MonoKind -> Term Prd -> Term Cns -> Command
  Print  :: Loc -> Term Prd -> Command -> Command
  Read   :: Loc -> Term Cns -> Command
  Jump   :: Loc -> FreeVarName -> Command
  ExitSuccess :: Loc -> Command
  ExitFailure :: Loc -> Command
  PrimOp :: Loc -> PrimitiveType -> PrimitiveOp -> Substitution -> Command

deriving instance Eq Command
deriving instance Show Command


---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

pctermOpeningRec :: Int -> Substitution -> PrdCnsTerm -> PrdCnsTerm
pctermOpeningRec k subst (PrdTerm tm) = PrdTerm $ termOpeningRec k subst tm
pctermOpeningRec k subst (CnsTerm tm) = CnsTerm $ termOpeningRec k subst tm

termOpeningRec :: Int -> Substitution -> Term pc -> Term pc
termOpeningRec k subst bv@(BoundVar _ pcrep(i,j)) | i == k    = case (pcrep, subst !! j) of
                                                                     (PrdRep, PrdTerm tm) -> tm
                                                                     (CnsRep, CnsTerm tm) -> tm
                                                                     _                    -> error "termOpeningRec BOOM"
                                                  | otherwise = bv
termOpeningRec _ _ fv@FreeVar{} = fv
termOpeningRec k args (Xtor loc annot rep ns xt subst) =
  Xtor loc annot rep ns xt (pctermOpeningRec k args <$> subst)
termOpeningRec k args (XCase loc annot rep ns cases) =
  XCase loc annot rep ns $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args cmdcase_cmd }) cases
termOpeningRec k args (MuAbs loc annot rep fv cmd) =
  MuAbs loc annot rep fv (commandOpeningRec (k+1) args cmd)
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
commandOpeningRec k args (Apply loc annot kind t1 t2) =
  Apply loc annot kind (termOpeningRec k args t1) (termOpeningRec k args t2)
commandOpeningRec k args (PrimOp loc pt op subst) =
  PrimOp loc pt op (pctermOpeningRec k args <$> subst)

commandOpening :: Substitution -> Command -> Command
commandOpening = commandOpeningRec 0

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
  Xtor loc annot pc ns xt (pctermClosingRec k vars <$> subst)
termClosingRec k vars (XCase loc annot pc sn cases) =
  XCase loc annot pc sn $ map (\pmcase@MkCmdCase { cmdcase_cmd } -> pmcase { cmdcase_cmd = commandClosingRec (k+1) vars cmdcase_cmd }) cases
termClosingRec k vars (MuAbs loc annot pc fv cmd) =
  MuAbs loc annot pc fv (commandClosingRec (k+1) vars cmd)
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
commandClosingRec k args (Apply ext annot kind t1 t2) =
  Apply ext annot kind (termClosingRec k args t1) (termClosingRec k args t2)
commandClosingRec k args (PrimOp ext pt op subst) =
  PrimOp ext pt op (pctermClosingRec k args <$> subst)

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
termLocallyClosedRec env (BoundVar _ pc idx) = checkIfBound env pc idx
termLocallyClosedRec _ FreeVar{} = Right ()
termLocallyClosedRec env (Xtor _ _ _ _ _ subst) = do
  sequence_ (pctermLocallyClosedRec env <$> subst)
termLocallyClosedRec env (XCase _ _ _ _ cases) = do
  sequence_ ((\MkCmdCase { cmdcase_cmd, cmdcase_pat = XtorPat _ _ args } -> commandLocallyClosedRec (((\(x,_) -> (x,())) <$> args) : env) cmdcase_cmd) <$> cases)
termLocallyClosedRec env (MuAbs _ _ PrdRep _ cmd) = commandLocallyClosedRec ([(Cns,())] : env) cmd
termLocallyClosedRec env (MuAbs _ _ CnsRep _ cmd) = commandLocallyClosedRec ([(Prd,())] : env) cmd
termLocallyClosedRec _ (PrimLitI64 _ _) = Right ()
termLocallyClosedRec _ (PrimLitF64 _ _) = Right ()

commandLocallyClosedRec :: [[(PrdCns,())]] -> Command -> Either Error ()
commandLocallyClosedRec _ (ExitSuccess _) = Right ()
commandLocallyClosedRec _ (ExitFailure _) = Right ()
commandLocallyClosedRec _ (Jump _ _) = Right ()
commandLocallyClosedRec env (Print _ t cmd) = termLocallyClosedRec env t >> commandLocallyClosedRec env cmd
commandLocallyClosedRec env (Read _ cns) = termLocallyClosedRec env cns
commandLocallyClosedRec env (Apply _ _ _ t1 t2) = termLocallyClosedRec env t1 >> termLocallyClosedRec env t2
commandLocallyClosedRec env (PrimOp _ _ _ subst) = sequence_ $ pctermLocallyClosedRec env <$> subst

termLocallyClosed :: Term pc -> Either Error ()
termLocallyClosed = termLocallyClosedRec []

---------------------------------------------------------------------------------
-- Shifting
--
-- Used in program transformations like focusing.
---------------------------------------------------------------------------------

shiftPCTermRec :: ShiftDirection -> Int -> PrdCnsTerm -> PrdCnsTerm
shiftPCTermRec dir n (PrdTerm tm) = PrdTerm $ shiftTermRec dir n tm
shiftPCTermRec dir n (CnsTerm tm) = CnsTerm $ shiftTermRec dir n tm

shiftTermRec :: ShiftDirection -> Int -> Term pc -> Term pc
-- If (n <= i), then the bound variable was free from the position where shift was called.
shiftTermRec ShiftUp n (BoundVar loc pcrep (i,j)) | n <= i    = BoundVar loc pcrep (i + 1, j)
                                                  | otherwise = BoundVar loc pcrep (i    , j)
shiftTermRec ShiftDown n (BoundVar loc pcrep (i,j)) | n <= i    = BoundVar loc pcrep (i - 1, j)
                                                    | otherwise = BoundVar loc pcrep (i    , j)                                        
shiftTermRec _ _ var@FreeVar {} = var
shiftTermRec dir n (Xtor loc annot pcrep ns xt subst) =
    Xtor loc annot pcrep ns xt (shiftPCTermRec dir n <$> subst)
shiftTermRec dir n (XCase loc annot pcrep ns cases) =
  XCase loc annot pcrep ns (shiftCmdCaseRec dir (n + 1) <$> cases)
shiftTermRec dir n (MuAbs loc annot pcrep bs cmd) =
  MuAbs loc annot pcrep bs (shiftCmdRec dir (n + 1) cmd)
shiftTermRec _ _ lit@PrimLitI64{} = lit
shiftTermRec _ _ lit@PrimLitF64{} = lit

shiftCmdCaseRec :: ShiftDirection -> Int -> CmdCase -> CmdCase
shiftCmdCaseRec dir n (MkCmdCase ext pat cmd) = MkCmdCase ext pat (shiftCmdRec dir n cmd)

shiftCmdRec :: ShiftDirection -> Int -> Command -> Command
shiftCmdRec dir n (Apply loc annot kind prd cns) = Apply loc annot kind (shiftTermRec dir n prd) (shiftTermRec dir n cns)
shiftCmdRec _ _ (ExitSuccess ext) = ExitSuccess ext
shiftCmdRec _ _ (ExitFailure ext) = ExitFailure ext
shiftCmdRec dir n (Print ext prd cmd) = Print ext (shiftTermRec dir n prd) (shiftCmdRec dir n cmd)
shiftCmdRec dir n (Read ext cns) = Read ext (shiftTermRec dir n cns)
shiftCmdRec _ _ (Jump ext fv) = Jump ext fv
shiftCmdRec dir n (PrimOp ext pt op subst) = PrimOp ext pt op (shiftPCTermRec dir n <$> subst)

-- | Shift all unbound BoundVars up by one.
shiftCmd :: ShiftDirection -> Command -> Command
shiftCmd dir = shiftCmdRec dir 0

