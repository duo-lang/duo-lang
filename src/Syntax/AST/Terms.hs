module Syntax.AST.Terms where

import Data.List (elemIndex)
import Data.Maybe (fromJust, isJust)
import Data.Text qualified as T

import Utils
import Errors
import Syntax.Common
import Syntax.AST.Types

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

-- | A SubstitutionI is like a substitution where one of the arguments has been
-- replaced by an implicit argument. The following convention for the use of the
-- `pc` parameter is used:
--
-- SubstitutionI ext Prd = ... [*] ...
-- SubstitutionI ext Cns = ... (*) ...
type SubstitutionI (pc :: PrdCns) = (Substitution, PrdCnsRep pc, Substitution)

---------------------------------------------------------------------------------
-- Pattern/copattern match cases
---------------------------------------------------------------------------------

-- | Represents one case in a pattern match or copattern match.
-- The `ext` field is used to save additional information, such as source code locations.
--
--        X(x_1,...,x_n) => e
--        ^ ^^^^^^^^^^^     ^
--        |      |          |
--        |  tmcase_args  tmcase_term
--        |
--    tmcase_name
--
data TermCase = MkTermCase
  { tmcase_ext  :: Loc
  , tmcase_name :: XtorName
  , tmcase_args :: [(PrdCns, Maybe FreeVarName)]
  , tmcase_term :: Term Prd
  }

deriving instance Eq TermCase
deriving instance Show TermCase

-- | Represents one case in a pattern match or copattern match.
-- Does bind an implicit argument (in contrast to TermCase).
-- The `ext` field is used to save additional information, such as source code locations.
--
--        X(x_1, * ,x_n) => e
--        ^ ^^^^^^^^^^^     ^
--        |      |          |
--        |  tmcasei_args  tmcasei_term
--        |
--    tmcasei_name
--
data TermCaseI = MkTermCaseI
  { tmcasei_ext  :: Loc
  , tmcasei_name :: XtorName
  -- | The pattern arguments
  -- The empty tuple stands for the implicit argument (*)
  , tmcasei_args :: ([(PrdCns, Maybe FreeVarName)], (), [(PrdCns, Maybe FreeVarName)])
  , tmcasei_term :: Term Prd
  }

deriving instance Eq TermCaseI
deriving instance Show TermCaseI

-- | Represents one case in a pattern match or copattern match.
--
--        X Gamma           => c
--        ^ ^^^^^-----         ^------
--        |          |               |
--    cmdcase_name  cmdcase_args      cmdcase_cmd
--
data CmdCase = MkCmdCase
  { cmdcase_ext  :: Loc
  , cmdcase_name :: XtorName
  , cmdcase_args :: [(PrdCns, Maybe FreeVarName)]
  , cmdcase_cmd  :: Command
  }

deriving instance Eq CmdCase
deriving instance Show CmdCase

---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

-- | A symmetric term.
-- The `bs` parameter is used to store additional information at binding sites.
data Term (pc :: PrdCns) where
  -- | A bound variable in the locally nameless system.
  BoundVar :: Loc -> PrdCnsRep pc -> Maybe (Typ (PrdCnsToPol pc)) -> Index -> Term pc
  -- | A free variable in the locally nameless system.
  FreeVar :: Loc -> PrdCnsRep pc -> Maybe (Typ (PrdCnsToPol pc)) -> FreeVarName -> Term pc
  -- | A constructor or destructor.
  -- If the first argument is `PrdRep` it is a constructor, a destructor otherwise.
  Xtor :: Loc -> PrdCnsRep pc -> Maybe (Typ (PrdCnsToPol pc)) -> NominalStructural -> XtorName -> Substitution -> Term pc
  -- | A pattern or copattern match.
  -- If the first argument is `PrdRep` it is a copattern match, a pattern match otherwise.
  XMatch :: Loc -> PrdCnsRep pc -> Maybe (Typ (PrdCnsToPol pc)) -> NominalStructural -> [CmdCase] -> Term pc
  -- | A Mu or TildeMu abstraction:
  --
  --  mu k.c    =   MuAbs PrdRep c
  -- ~mu x.c    =   MuAbs CnsRep c
  MuAbs :: Loc -> PrdCnsRep pc -> Maybe (Typ (PrdCnsToPol pc)) -> Maybe FreeVarName -> Command -> Term pc
  --
  -- Syntactic Sugar
  --
  Dtor :: Loc -> PrdCnsRep pc -> Maybe (Typ (PrdCnsToPol pc)) -> NominalStructural ->  XtorName -> Term Prd -> SubstitutionI pc -> Term pc
  -- | A pattern match:
  --
  -- case e of { ... }
  --
  Case :: Loc -> Maybe (Typ Pos) -> NominalStructural -> Term Prd -> [TermCase] -> Term Prd
  -- | A copattern match:
  --
  -- cocase { ... }
  --
  Cocase :: Loc -> Maybe (Typ Pos) -> NominalStructural -> [TermCaseI] -> Term Prd
  -- | Primitive literals
  PrimLitI64 :: Loc -> Integer -> Term Prd
  PrimLitF64 :: Loc -> Double -> Term Prd

deriving instance Eq (Term Prd)
deriving instance Eq (Term Cns)
deriving instance Show (Term Prd)
deriving instance Show (Term Cns)

getTypeTerm' :: forall pc. Term pc -> Maybe (Typ (PrdCnsToPol pc))
getTypeTerm' (BoundVar _ _ annot _)   = annot
getTypeTerm' (FreeVar  _ _ annot _)   = annot
getTypeTerm' (Xtor _ _ annot _ _ _)   = annot
getTypeTerm' (XMatch _ _ annot _ _)   = annot
getTypeTerm' (MuAbs _ _ annot _ _)    = annot
getTypeTerm' (Dtor _ _ annot _ _ _ _) = annot
getTypeTerm' (Case _ annot _ _ _)     = annot
getTypeTerm' (Cocase _ annot _ _)     = annot
getTypeTerm' (PrimLitI64 _ _)         = Just (TyPrim PosRep I64)
getTypeTerm' (PrimLitF64 _ _)         = Just (TyPrim PosRep F64)

getTypeTerm :: forall pc. Term pc -> Typ (PrdCnsToPol pc)
getTypeTerm tm = case getTypeTerm' tm of
  Nothing -> error "Boom"
  Just typ -> typ

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

deriving instance Eq Command
deriving instance Show Command


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
termOpeningRec k args (XMatch loc rep annot ns cases) =
  XMatch loc rep annot ns $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args cmdcase_cmd }) cases
termOpeningRec k args (MuAbs loc rep annot fv cmd) =
  MuAbs loc rep annot fv (commandOpeningRec (k+1) args cmd)
-- ATerms
termOpeningRec k args (Dtor loc rep annot ns xt t (args1,pcrep,args2)) =
  let
    args1' = pctermOpeningRec k args <$> args1
    args2' = pctermOpeningRec k args <$> args2
  in
    Dtor loc rep annot ns xt (termOpeningRec k args t) (args1', pcrep, args2')
termOpeningRec k args (Case loc annot ns t cases) =
  Case loc annot ns (termOpeningRec k args t) ((\pmcase@MkTermCase { tmcase_term } -> pmcase { tmcase_term = termOpeningRec (k + 1) args tmcase_term }) <$> cases)
termOpeningRec k args (Cocase loc annot ns cocases) =
  Cocase loc annot ns ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termOpeningRec (k + 1) args tmcasei_term }) <$> cocases)
termOpeningRec _ _ lit@PrimLitI64{} = lit
termOpeningRec _ _ lit@PrimLitF64{} = lit


commandOpeningRec :: Int -> Substitution -> Command -> Command
commandOpeningRec _ _ (ExitSuccess loc) = ExitSuccess loc
commandOpeningRec _ _ (ExitFailure loc) = ExitFailure loc
commandOpeningRec k args (Print loc t cmd) = Print loc (termOpeningRec k args t) (commandOpeningRec k args cmd)
commandOpeningRec k args (Read loc cns) = Read loc (termOpeningRec k args cns)
commandOpeningRec _ _ (Jump loc fv) = Jump loc fv
commandOpeningRec k args (Apply loc kind t1 t2) = Apply loc kind (termOpeningRec k args t1) (termOpeningRec k args t2)
commandOpeningRec k args (PrimOp loc pt op subst) = PrimOp loc pt op (pctermOpeningRec k args <$> subst)

commandOpening :: Substitution -> Command -> Command
commandOpening = commandOpeningRec 0

termOpening :: Substitution -> Term pc -> Term pc
termOpening = termOpeningRec 0

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
termClosingRec k vars (XMatch loc pc annot sn cases) =
  XMatch loc pc annot sn $ map (\pmcase@MkCmdCase { cmdcase_cmd } -> pmcase { cmdcase_cmd = commandClosingRec (k+1) vars cmdcase_cmd }) cases
termClosingRec k vars (MuAbs loc pc annot fv cmd) =
  MuAbs loc pc annot fv (commandClosingRec (k+1) vars cmd)
-- ATerms
termClosingRec k args (Dtor loc pc annot ns xt t (args1,pcrep,args2)) =
  let
    args1' = pctermClosingRec k args <$> args1
    args2' = pctermClosingRec k args <$> args2
  in
    Dtor loc pc annot ns xt (termClosingRec k args t) (args1', pcrep, args2')
termClosingRec k args (Case loc annot ns t cases) =
  Case loc annot ns (termClosingRec k args t) ((\pmcase@MkTermCase { tmcase_term } -> pmcase { tmcase_term = termClosingRec (k + 1) args tmcase_term }) <$> cases)
termClosingRec k args (Cocase loc annot ns cocases) =
  Cocase loc annot ns ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termClosingRec (k + 1) args tmcasei_term }) <$> cocases)
termClosingRec _ _ lit@PrimLitI64{} = lit
termClosingRec _ _ lit@PrimLitF64{} = lit

commandClosingRec :: Int -> [(PrdCns, FreeVarName)] -> Command -> Command
commandClosingRec _ _ (ExitSuccess ext) = ExitSuccess ext
commandClosingRec _ _ (ExitFailure ext) = ExitFailure ext
commandClosingRec _ _ (Jump ext fv) = Jump ext fv
commandClosingRec k args (Print ext t cmd) = Print ext (termClosingRec k args t) (commandClosingRec k args cmd)
commandClosingRec k args (Read ext cns) = Read ext (termClosingRec k args cns)
commandClosingRec k args (Apply ext kind t1 t2) = Apply ext kind (termClosingRec k args t1) (termClosingRec k args t2)
commandClosingRec k args (PrimOp ext pt op subst) = PrimOp ext pt op (pctermClosingRec k args <$> subst)

termClosing :: [(PrdCns, FreeVarName)] -> Term pc -> Term pc
termClosing = termClosingRec 0

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
termLocallyClosedRec env (XMatch _ _ _ _ cases) = do
  sequence_ ((\MkCmdCase { cmdcase_cmd, cmdcase_args } -> commandLocallyClosedRec (((\(x,_) -> (x,())) <$> cmdcase_args) : env) cmdcase_cmd) <$> cases)
termLocallyClosedRec env (MuAbs _ PrdRep _ _ cmd) = commandLocallyClosedRec ([(Cns,())] : env) cmd
termLocallyClosedRec env (MuAbs _ CnsRep _ _ cmd) = commandLocallyClosedRec ([(Prd,())] : env) cmd
termLocallyClosedRec env (Dtor _ _ _ _ _ e (args1,_,args2)) = do
  termLocallyClosedRec env e
  sequence_ (pctermLocallyClosedRec env <$> args1)
  sequence_ (pctermLocallyClosedRec env <$> args2)
termLocallyClosedRec env (Case _ _ _ e cases) = do
  termLocallyClosedRec env e
  sequence_ (termCaseLocallyClosedRec env <$> cases)
termLocallyClosedRec env (Cocase _ _ _ cases) =
  sequence_ (termCaseILocallyClosedRec env <$> cases)
termLocallyClosedRec _ (PrimLitI64 _ _) = Right ()
termLocallyClosedRec _ (PrimLitF64 _ _) = Right ()

termCaseLocallyClosedRec :: [[(PrdCns,())]] -> TermCase -> Either Error ()
termCaseLocallyClosedRec env (MkTermCase _ _ args e) = do
  termLocallyClosedRec (((\(x,_) -> (x,())) <$> args):env) e

termCaseILocallyClosedRec :: [[(PrdCns,())]] -> TermCaseI -> Either Error ()
termCaseILocallyClosedRec env (MkTermCaseI _ _ (as1, (), as2) e) =
  let newArgs = (\(x,_) -> (x,())) <$> as1 ++ [(Cns, Nothing)] ++ as2 in
  termLocallyClosedRec (newArgs:env) e

commandLocallyClosedRec :: [[(PrdCns,())]] -> Command -> Either Error ()
commandLocallyClosedRec _ (ExitSuccess _) = Right ()
commandLocallyClosedRec _ (ExitFailure _) = Right ()
commandLocallyClosedRec _ (Jump _ _) = Right ()
commandLocallyClosedRec env (Print _ t cmd) = termLocallyClosedRec env t >> commandLocallyClosedRec env cmd
commandLocallyClosedRec env (Read _ cns) = termLocallyClosedRec env cns
commandLocallyClosedRec env (Apply _ _ t1 t2) = termLocallyClosedRec env t1 >> termLocallyClosedRec env t2
commandLocallyClosedRec env (PrimOp _ _ _ subst) = sequence_ $ pctermLocallyClosedRec env <$> subst

termLocallyClosed :: Term pc -> Either Error ()
termLocallyClosed = termLocallyClosedRec []

commandLocallyClosed :: Command -> Either Error ()
commandLocallyClosed = commandLocallyClosedRec []

---------------------------------------------------------------------------------
-- These functions  translate a locally nameless term into a named representation.
--
-- Use only for prettyprinting! These functions only "undo" the steps in the parser
-- and do not fulfil any semantic properties w.r.t shadowing etc.!
---------------------------------------------------------------------------------

freeVarNamesToXtorArgs :: [(PrdCns, Maybe FreeVarName)] -> Substitution
freeVarNamesToXtorArgs bs = f <$> bs
  where
    f (Prd, Nothing) = error "Create Names first!"
    f (Prd, Just fv) = PrdTerm $ FreeVar defaultLoc PrdRep Nothing fv
    f (Cns, Nothing) = error "Create Names first!"
    f (Cns, Just fv) = CnsTerm $ FreeVar defaultLoc CnsRep Nothing fv

openTermCase :: TermCase -> TermCase
openTermCase MkTermCase { tmcase_ext, tmcase_name, tmcase_args, tmcase_term } =
    MkTermCase { tmcase_ext = tmcase_ext
               , tmcase_name = tmcase_name
               , tmcase_args = tmcase_args
               , tmcase_term = termOpening (freeVarNamesToXtorArgs tmcase_args) (openTermComplete tmcase_term)
               }

openTermCaseI :: TermCaseI -> TermCaseI
openTermCaseI MkTermCaseI { tmcasei_ext, tmcasei_name, tmcasei_args = (as1, (), as2), tmcasei_term } =
  MkTermCaseI { tmcasei_ext = tmcasei_ext
              , tmcasei_name = tmcasei_name
              , tmcasei_args = (as1, (), as2)
              , tmcasei_term = termOpening (freeVarNamesToXtorArgs (as1 ++ [(Cns, Nothing)] ++ as2)) (openTermComplete tmcasei_term)
              }

openCmdCase :: CmdCase -> CmdCase
openCmdCase MkCmdCase { cmdcase_ext, cmdcase_name, cmdcase_args, cmdcase_cmd } =
  MkCmdCase { cmdcase_ext = cmdcase_ext
            , cmdcase_name = cmdcase_name
            , cmdcase_args = cmdcase_args
            , cmdcase_cmd = commandOpening (freeVarNamesToXtorArgs cmdcase_args) (openCommandComplete cmdcase_cmd)
            }

openPCTermComplete :: PrdCnsTerm -> PrdCnsTerm
openPCTermComplete (PrdTerm tm) = PrdTerm $ openTermComplete tm
openPCTermComplete (CnsTerm tm) = CnsTerm $ openTermComplete tm

openTermComplete :: Term pc -> Term pc
openTermComplete (BoundVar loc pc annot idx) = BoundVar loc pc annot idx
openTermComplete (FreeVar loc pc annot v) = FreeVar loc pc annot v
openTermComplete (Xtor loc pc annot ns xt args) = Xtor loc pc annot ns xt (openPCTermComplete <$> args)
openTermComplete (XMatch loc pc annot ns cases) = XMatch loc pc annot ns (openCmdCase <$> cases)
openTermComplete (MuAbs loc PrdRep annot (Just fv) cmd) =
  MuAbs loc PrdRep annot (Just fv) (commandOpening [CnsTerm (FreeVar defaultLoc CnsRep Nothing fv)] (openCommandComplete cmd))
openTermComplete (MuAbs loc CnsRep annot (Just fv) cmd) =
  MuAbs loc CnsRep annot (Just fv) (commandOpening [PrdTerm (FreeVar defaultLoc PrdRep Nothing fv)] (openCommandComplete cmd))
openTermComplete (MuAbs _ _ _ Nothing _) = error "Create names first!"
openTermComplete (Dtor loc rep annot ns xt t (args1,pcrep,args2)) =
  Dtor loc rep annot ns xt (openTermComplete t) (openPCTermComplete <$> args1,pcrep, openPCTermComplete <$> args2)
openTermComplete (Case loc annot ns t cases) = Case loc annot ns (openTermComplete t) (openTermCase <$> cases)
openTermComplete (Cocase loc annot ns cocases) = Cocase loc annot ns (openTermCaseI <$> cocases)
openTermComplete (PrimLitI64 loc i) = PrimLitI64 loc i
openTermComplete (PrimLitF64 loc d) = PrimLitF64 loc d

openCommandComplete :: Command -> Command
openCommandComplete (Apply loc kind t1 t2) = Apply loc kind (openTermComplete t1) (openTermComplete t2)
openCommandComplete (Print loc t cmd) = Print loc (openTermComplete t) (openCommandComplete cmd)
openCommandComplete (Read loc cns) = Read loc (openTermComplete cns)
openCommandComplete (Jump loc fv) = Jump loc fv
openCommandComplete (ExitSuccess loc) = ExitSuccess loc
openCommandComplete (ExitFailure loc) = ExitFailure loc
openCommandComplete (PrimOp loc pt op subst) = PrimOp loc pt op (openPCTermComplete <$> subst)

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
shiftTermRec n (XMatch loc pcrep annot ns cases) =
  XMatch loc pcrep annot ns (shiftCmdCaseRec (n + 1) <$> cases)
shiftTermRec n (MuAbs loc pcrep annot bs cmd) =
  MuAbs loc pcrep annot bs (shiftCmdRec (n + 1) cmd)
shiftTermRec n (Dtor loc pcrep annot ns xt e (args1,pcrep',args2)) =
  Dtor loc pcrep annot ns xt (shiftTermRec n e) (shiftPCTermRec n <$> args1,pcrep',shiftPCTermRec n <$> args2)
shiftTermRec n (Case loc annot ns e cases) =
  Case loc annot ns (shiftTermRec n e) (shiftTermCaseRec n <$> cases)
shiftTermRec n (Cocase loc annot ns cases) =
  Cocase loc annot ns (shiftTermCaseIRec n <$> cases)
shiftTermRec _ lit@PrimLitI64{} = lit
shiftTermRec _ lit@PrimLitF64{} = lit

shiftTermCaseRec :: Int -> TermCase -> TermCase
shiftTermCaseRec n (MkTermCase ext xt args e) = MkTermCase ext xt args (shiftTermRec n e)

shiftTermCaseIRec :: Int -> TermCaseI -> TermCaseI
shiftTermCaseIRec n (MkTermCaseI ext xt args e) = MkTermCaseI ext xt args (shiftTermRec n e)

shiftCmdCaseRec :: Int -> CmdCase -> CmdCase
shiftCmdCaseRec n (MkCmdCase ext name bs cmd) = MkCmdCase ext name bs (shiftCmdRec n cmd)

shiftCmdRec :: Int -> Command -> Command
shiftCmdRec n (Apply ext kind prd cns) = Apply ext kind (shiftTermRec n prd) (shiftTermRec n cns)
shiftCmdRec _ (ExitSuccess ext) = ExitSuccess ext
shiftCmdRec _ (ExitFailure ext) = ExitFailure ext
shiftCmdRec n (Print ext prd cmd) = Print ext (shiftTermRec n prd) (shiftCmdRec n cmd)
shiftCmdRec n (Read ext cns) = Read ext (shiftTermRec n cns)
shiftCmdRec _ (Jump ext fv) = Jump ext fv
shiftCmdRec n (PrimOp ext pt op subst) = PrimOp ext pt op (shiftPCTermRec n <$> subst)

-- | Shift all unbound BoundVars up by one.
shiftTerm :: Term pc -> Term pc
shiftTerm = shiftTermRec 0

-- | Shift all unbound BoundVars up by one.
shiftCmd :: Command -> Command
shiftCmd = shiftCmdRec 0

---------------------------------------------------------------------------------
-- Remove Names
--
-- Replaces all variable binding sites with Nothing
---------------------------------------------------------------------------------

removeNamesPrdCnsTerm :: PrdCnsTerm -> PrdCnsTerm
removeNamesPrdCnsTerm (PrdTerm tm) = PrdTerm $ removeNamesTerm tm
removeNamesPrdCnsTerm (CnsTerm tm) = CnsTerm $ removeNamesTerm tm

removeNamesTerm :: Term pc -> Term pc
removeNamesTerm f@FreeVar{} = f
removeNamesTerm f@BoundVar{} = f
removeNamesTerm (Xtor loc pc annot ns xt args) = Xtor loc pc annot ns xt (removeNamesPrdCnsTerm <$> args)
removeNamesTerm (MuAbs loc pc annot _ cmd) = MuAbs loc pc annot Nothing (removeNamesCmd cmd)
removeNamesTerm (XMatch loc pc annot ns cases) = XMatch loc pc annot ns (removeNamesCmdCase <$> cases)
removeNamesTerm (Dtor loc pc annot ns xt e (args1,pcrep,args2)) =
  Dtor loc pc annot ns xt (removeNamesTerm e) (removeNamesPrdCnsTerm <$> args1,pcrep,removeNamesPrdCnsTerm <$> args2)
removeNamesTerm (Case loc annot ns e cases) = Case loc annot ns (removeNamesTerm e) (removeNamesTermCase <$> cases)
removeNamesTerm (Cocase loc annot ns cases) = Cocase loc annot ns (removeNamesTermCaseI <$> cases)
removeNamesTerm lit@PrimLitI64{} = lit
removeNamesTerm lit@PrimLitF64{} = lit

removeNamesTermCase :: TermCase -> TermCase
removeNamesTermCase (MkTermCase ext xt args e)   = MkTermCase ext xt ((\(pc,_) -> (pc,Nothing)) <$> args) (removeNamesTerm e)

removeNamesTermCaseI :: TermCaseI -> TermCaseI
removeNamesTermCaseI (MkTermCaseI ext xt (as1, (), as2) e) =
  let r = \(pc,_) -> (pc, Nothing) in
  MkTermCaseI ext xt (r <$> as1, (), r <$> as2) (removeNamesTerm e)

removeNamesCmdCase :: CmdCase -> CmdCase
removeNamesCmdCase (MkCmdCase ext xt args cmd) = MkCmdCase ext xt ((\(pc,_) -> (pc,Nothing)) <$> args) (removeNamesCmd cmd)

removeNamesCmd :: Command -> Command
removeNamesCmd (Apply ext kind prd cns) = Apply ext kind (removeNamesTerm prd) (removeNamesTerm cns)
removeNamesCmd (Print ext prd cmd) = Print ext (removeNamesTerm prd) (removeNamesCmd cmd)
removeNamesCmd (Read ext cns) = Read ext (removeNamesTerm cns)
removeNamesCmd (Jump ext fv) = Jump ext fv
removeNamesCmd (ExitSuccess ext) = ExitSuccess ext
removeNamesCmd (ExitFailure ext) = ExitFailure ext
removeNamesCmd (PrimOp ext pt op subst) = PrimOp ext pt op (removeNamesPrdCnsTerm <$> subst)
