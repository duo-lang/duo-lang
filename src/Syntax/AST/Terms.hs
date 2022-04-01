module Syntax.AST.Terms where

import Data.Kind (Type)
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

data PrdCnsTerm (ext :: Phase) where
  PrdTerm :: Term Prd ext -> PrdCnsTerm ext
  CnsTerm :: Term Cns ext -> PrdCnsTerm ext

deriving instance (Eq (PrdCnsTerm Parsed))
deriving instance (Eq (PrdCnsTerm Inferred))
deriving instance (Eq (PrdCnsTerm Compiled))
deriving instance (Show (PrdCnsTerm Parsed))
deriving instance (Show (PrdCnsTerm Inferred))
deriving instance (Show (PrdCnsTerm Compiled))

type Substitution (ext :: Phase) = [PrdCnsTerm ext]

-- | A SubstitutionI is like a substitution where one of the arguments has been
-- replaced by an implicit argument. The following convention for the use of the
-- `pc` parameter is used:
--
-- SubstitutionI ext Prd = ... [*] ...
-- SubstitutionI ext Cns = ... (*) ...
type SubstitutionI (ext :: Phase) (pc :: PrdCns) = (Substitution ext, PrdCnsRep pc, Substitution ext)

---------------------------------------------------------------------------------
-- Pattern/copattern match cases
---------------------------------------------------------------------------------

type family CaseExt (ext :: Phase) :: Type where
  CaseExt Parsed   = Loc
  CaseExt Inferred = Loc
  CaseExt Compiled = ()

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
data TermCase (ext :: Phase) = MkTermCase
  { tmcase_ext  :: CaseExt ext
  , tmcase_name :: XtorName
  , tmcase_args :: [(PrdCns, Maybe FreeVarName)]
  , tmcase_term :: Term Prd ext
  }

deriving instance (Eq (TermCase Parsed))
deriving instance (Eq (TermCase Inferred))
deriving instance (Eq (TermCase Compiled))
deriving instance (Show (TermCase Parsed))
deriving instance (Show (TermCase Inferred))
deriving instance (Show (TermCase Compiled))

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
data TermCaseI (ext :: Phase) = MkTermCaseI
  { tmcasei_ext  :: CaseExt ext
  , tmcasei_name :: XtorName
  -- | The pattern arguments
  -- The empty tuple stands for the implicit argument (*)
  , tmcasei_args :: ([(PrdCns, Maybe FreeVarName)], (), [(PrdCns, Maybe FreeVarName)])
  , tmcasei_term :: Term Prd ext
  }

deriving instance (Eq (TermCaseI Parsed))
deriving instance (Eq (TermCaseI Inferred))
deriving instance (Eq (TermCaseI Compiled))
deriving instance (Show (TermCaseI Parsed))
deriving instance (Show (TermCaseI Inferred))
deriving instance (Show (TermCaseI Compiled))

-- | Represents one case in a pattern match or copattern match.
--
--        X Gamma           => c
--        ^ ^^^^^-----         ^------
--        |          |               |
--    cmdcase_name  cmdcase_args      cmdcase_cmd
--
data CmdCase (ext :: Phase) = MkCmdCase
  { cmdcase_ext  :: CaseExt ext
  , cmdcase_name :: XtorName
  , cmdcase_args :: [(PrdCns, Maybe FreeVarName)]
  , cmdcase_cmd  :: Command ext
  }

deriving instance (Eq (CmdCase Parsed))
deriving instance (Eq (CmdCase Inferred))
deriving instance (Eq (CmdCase Compiled))
deriving instance (Show (CmdCase Parsed))
deriving instance (Show (CmdCase Inferred))
deriving instance (Show (CmdCase Compiled))

---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

type family TermExt (pc :: PrdCns) (ext :: Phase) :: Type where
  TermExt _ Parsed = Loc
  TermExt rep Inferred = (Loc, Typ (PrdCnsToPol rep))
  TermExt _ Compiled = ()

-- | A symmetric term.
-- The `bs` parameter is used to store additional information at binding sites.
data Term (pc :: PrdCns) (ext :: Phase) where
  -- | A bound variable in the locally nameless system.
  BoundVar :: TermExt pc ext -> PrdCnsRep pc -> Index -> Term pc ext
  -- | A free variable in the locally nameless system.
  FreeVar :: TermExt pc ext -> PrdCnsRep pc -> FreeVarName -> Term pc ext
  -- | A constructor or destructor.
  -- If the first argument is `PrdRep` it is a constructor, a destructor otherwise.
  Xtor :: TermExt pc ext -> PrdCnsRep pc -> NominalStructural -> XtorName -> Substitution ext -> Term pc ext
  -- | A pattern or copattern match.
  -- If the first argument is `PrdRep` it is a copattern match, a pattern match otherwise.
  XMatch :: TermExt pc ext -> PrdCnsRep pc -> NominalStructural -> [CmdCase ext] -> Term pc ext
  -- | A Mu or TildeMu abstraction:
  --
  --  mu k.c    =   MuAbs PrdRep c
  -- ~mu x.c    =   MuAbs CnsRep c
  MuAbs :: TermExt pc ext -> PrdCnsRep pc -> Maybe FreeVarName -> Command ext -> Term pc ext
  --
  -- Syntactic Sugar
  --
  Dtor :: TermExt pc ext -> NominalStructural -> XtorName -> Term Prd ext -> SubstitutionI ext pc -> Term pc ext
  -- | A pattern match:
  --
  -- case e of { ... }
  --
  Case :: TermExt Prd ext -> NominalStructural -> Term Prd ext -> [TermCase ext] -> Term Prd ext
  -- | A copattern match:
  --
  -- cocase { ... }
  --
  Cocase :: TermExt Prd ext -> NominalStructural -> [TermCaseI ext] -> Term Prd ext
  -- | Primitive literals
  PrimLitI64 :: TermExt Prd ext -> Integer -> Term Prd ext
  PrimLitF64 :: TermExt Prd ext -> Double -> Term Prd ext

deriving instance (Eq (Term pc Parsed))
deriving instance (Eq (Term Prd Inferred))
deriving instance (Eq (Term Cns Inferred))
deriving instance (Eq (Term pc Compiled))
deriving instance (Show (Term pc Parsed))
deriving instance (Show (Term Prd Inferred))
deriving instance (Show (Term Cns Inferred))
deriving instance (Show (Term pc Compiled))

getTypeTerm :: Term pc Inferred -> Typ (PrdCnsToPol pc)
getTypeTerm (BoundVar ext rep _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeTerm (FreeVar  ext rep _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeTerm (Xtor ext rep _ _ _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeTerm (XMatch   ext rep _ _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeTerm (MuAbs    ext rep _ _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeTerm (Dtor (_,ty) _ _ _ _) = ty
getTypeTerm (Case (_,ty) _ _ _)  = ty
getTypeTerm (Cocase (_,ty) _ _)  = ty
getTypeTerm (PrimLitI64 (_, ty) _) = ty
getTypeTerm (PrimLitF64 (_, ty) _) = ty

getTypArgs :: Substitution Inferred -> LinearContext Pos
getTypArgs subst = getTypArgs' <$> subst
  where
    getTypArgs' (PrdTerm tm) = PrdCnsType PrdRep $ getTypeTerm tm
    getTypArgs' (CnsTerm tm) = PrdCnsType CnsRep $ getTypeTerm tm


---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

type family CommandExt (ext :: Phase) :: Type where
  CommandExt Parsed = Loc
  CommandExt Inferred = Loc
  CommandExt Compiled = ()

-- | An executable command.
data Command (ext :: Phase) where
  -- | A producer applied to a consumer:
  --
  --   p >> c
  Apply  :: CommandExt ext -> Maybe MonoKind -> Term Prd ext -> Term Cns ext -> Command ext
  Print  :: CommandExt ext -> Term Prd ext -> Command ext -> Command ext
  Read   :: CommandExt ext -> Term Cns ext -> Command ext
  Jump   :: CommandExt ext -> FreeVarName -> Command ext
  ExitSuccess :: CommandExt ext -> Command ext
  ExitFailure :: CommandExt ext -> Command ext
  PrimOp :: CommandExt ext -> PrimitiveType -> PrimitiveOp -> Substitution ext -> Command ext

deriving instance (Eq (Command Parsed))
deriving instance (Eq (Command Inferred))
deriving instance (Eq (Command Compiled))
deriving instance (Show (Command Parsed))
deriving instance (Show (Command Inferred))
deriving instance (Show (Command Compiled))


---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

pctermOpeningRec :: Int -> Substitution Compiled -> PrdCnsTerm Compiled -> PrdCnsTerm Compiled
pctermOpeningRec k subst (PrdTerm tm) = PrdTerm $ termOpeningRec k subst tm
pctermOpeningRec k subst (CnsTerm tm) = CnsTerm $ termOpeningRec k subst tm

termOpeningRec :: Int -> Substitution Compiled -> Term pc Compiled -> Term pc Compiled
termOpeningRec k subst bv@(BoundVar _ pcrep (i,j)) | i == k    = case (pcrep, subst !! j) of
                                                                      (PrdRep, PrdTerm tm) -> tm
                                                                      (CnsRep, CnsTerm tm) -> tm
                                                                      _                    -> error "termOpeningRec BOOM"
                                                   | otherwise = bv
termOpeningRec _ _ fv@(FreeVar _ _ _)       = fv
termOpeningRec k args (Xtor _ s ns xt subst) =
  Xtor () s ns xt (pctermOpeningRec k args <$> subst)
termOpeningRec k args (XMatch _ pc sn cases) =
  XMatch () pc sn $ map (\pmcase@MkCmdCase{ cmdcase_cmd } -> pmcase { cmdcase_cmd = commandOpeningRec (k+1) args cmdcase_cmd }) cases
termOpeningRec k args (MuAbs _ pc a cmd) =
  MuAbs () pc a (commandOpeningRec (k+1) args cmd)
-- ATerms
termOpeningRec k args (Dtor _ ns xt t (args1,pcrep,args2)) =
  let
    args1' = pctermOpeningRec k args <$> args1
    args2' = pctermOpeningRec k args <$> args2
  in
    Dtor () ns xt (termOpeningRec k args t) (args1', pcrep, args2')
termOpeningRec k args (Case _ ns t cases) =
  Case () ns (termOpeningRec k args t) ((\pmcase@MkTermCase { tmcase_term } -> pmcase { tmcase_term = termOpeningRec (k + 1) args tmcase_term }) <$> cases)
termOpeningRec k args (Cocase _ ns cocases) =
  Cocase () ns ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termOpeningRec (k + 1) args tmcasei_term }) <$> cocases)
termOpeningRec _ _ lit@PrimLitI64{} = lit
termOpeningRec _ _ lit@PrimLitF64{} = lit


commandOpeningRec :: Int -> Substitution Compiled -> Command Compiled -> Command Compiled
commandOpeningRec _ _ (ExitSuccess _) = ExitSuccess ()
commandOpeningRec _ _ (ExitFailure _) = ExitFailure ()
commandOpeningRec k args (Print _ t cmd) = Print () (termOpeningRec k args t) (commandOpeningRec k args cmd)
commandOpeningRec k args (Read _ cns) = Read () (termOpeningRec k args cns)
commandOpeningRec _ _ (Jump _ fv) = Jump () fv
commandOpeningRec k args (Apply _ kind t1 t2) = Apply () kind (termOpeningRec k args t1) (termOpeningRec k args t2)
commandOpeningRec k args (PrimOp _ pt op subst) = PrimOp () pt op (pctermOpeningRec k args <$> subst)

commandOpening :: Substitution Compiled -> Command Compiled -> Command Compiled
commandOpening = commandOpeningRec 0

termOpening :: Substitution Compiled -> Term pc Compiled -> Term pc Compiled
termOpening = termOpeningRec 0

---------------------------------------------------------------------------------
-- Variable Closing
---------------------------------------------------------------------------------

pctermClosingRec :: Int -> [(PrdCns, FreeVarName)] -> PrdCnsTerm ext -> PrdCnsTerm ext
pctermClosingRec k vars (PrdTerm tm) = PrdTerm $ termClosingRec k vars tm
pctermClosingRec k vars (CnsTerm tm) = CnsTerm $ termClosingRec k vars tm

termClosingRec :: Int -> [(PrdCns, FreeVarName)] -> Term pc ext -> Term pc ext
termClosingRec _ _ bv@(BoundVar _ _ _) = bv
termClosingRec k vars (FreeVar ext PrdRep v) | isJust ((Prd,v) `elemIndex` vars) = BoundVar ext PrdRep (k, fromJust ((Prd,v) `elemIndex` vars))
                                             | otherwise = FreeVar ext PrdRep v
termClosingRec k vars (FreeVar ext CnsRep v) | isJust ((Cns,v) `elemIndex` vars) = BoundVar ext CnsRep (k, fromJust ((Cns,v) `elemIndex` vars))
                                             | otherwise = FreeVar ext CnsRep v
termClosingRec k vars (Xtor ext s ns xt subst) =
  Xtor ext s ns xt (pctermClosingRec k vars <$> subst)
termClosingRec k vars (XMatch ext pc sn cases) =
  XMatch ext pc sn $ map (\pmcase@MkCmdCase { cmdcase_cmd } -> pmcase { cmdcase_cmd = commandClosingRec (k+1) vars cmdcase_cmd }) cases
termClosingRec k vars (MuAbs ext pc a cmd) =
  MuAbs ext pc a (commandClosingRec (k+1) vars cmd)
-- ATerms
termClosingRec k args (Dtor ext ns xt t (args1,pcrep,args2)) =
  let
    args1' = pctermClosingRec k args <$> args1
    args2' = pctermClosingRec k args <$> args2
  in
    Dtor ext ns xt (termClosingRec k args t) (args1', pcrep, args2')
termClosingRec k args (Case ext ns t cases) =
  Case ext ns (termClosingRec k args t) ((\pmcase@MkTermCase { tmcase_term } -> pmcase { tmcase_term = termClosingRec (k + 1) args tmcase_term }) <$> cases)
termClosingRec k args (Cocase ext ns cocases) =
  Cocase ext ns ((\pmcase@MkTermCaseI { tmcasei_term } -> pmcase { tmcasei_term = termClosingRec (k + 1) args tmcasei_term }) <$> cocases)
termClosingRec _ _ lit@PrimLitI64{} = lit
termClosingRec _ _ lit@PrimLitF64{} = lit

commandClosingRec :: Int -> [(PrdCns, FreeVarName)] -> Command ext -> Command ext
commandClosingRec _ _ (ExitSuccess ext) = ExitSuccess ext
commandClosingRec _ _ (ExitFailure ext) = ExitFailure ext
commandClosingRec _ _ (Jump ext fv) = Jump ext fv
commandClosingRec k args (Print ext t cmd) = Print ext (termClosingRec k args t) (commandClosingRec k args cmd)
commandClosingRec k args (Read ext cns) = Read ext (termClosingRec k args cns)
commandClosingRec k args (Apply ext kind t1 t2) = Apply ext kind (termClosingRec k args t1) (termClosingRec k args t2)
commandClosingRec k args (PrimOp ext pt op subst) = PrimOp ext pt op (pctermClosingRec k args <$> subst)

termClosing :: [(PrdCns, FreeVarName)] -> Term pc ext -> Term pc ext
termClosing = termClosingRec 0

commandClosing :: [(PrdCns, FreeVarName)] -> Command ext -> Command ext
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

pctermLocallyClosedRec :: [[(PrdCns, ())]] -> PrdCnsTerm ext -> Either Error ()
pctermLocallyClosedRec env (PrdTerm tm) = termLocallyClosedRec env tm
pctermLocallyClosedRec env (CnsTerm tm) = termLocallyClosedRec env tm

termLocallyClosedRec :: [[(PrdCns,())]] -> Term pc ext -> Either Error ()
termLocallyClosedRec env (BoundVar _ pc idx) = checkIfBound env pc idx
termLocallyClosedRec _ (FreeVar _ _ _) = Right ()
termLocallyClosedRec env (Xtor _ _ _ _ subst) = do
  sequence_ (pctermLocallyClosedRec env <$> subst)
termLocallyClosedRec env (XMatch _ _ _ cases) = do
  sequence_ ((\MkCmdCase { cmdcase_cmd, cmdcase_args } -> commandLocallyClosedRec (((\(x,_) -> (x,())) <$> cmdcase_args) : env) cmdcase_cmd) <$> cases)
termLocallyClosedRec env (MuAbs _ PrdRep _ cmd) = commandLocallyClosedRec ([(Cns,())] : env) cmd
termLocallyClosedRec env (MuAbs _ CnsRep _ cmd) = commandLocallyClosedRec ([(Prd,())] : env) cmd
termLocallyClosedRec env (Dtor _ _ _ e (args1,_,args2)) = do
  termLocallyClosedRec env e
  sequence_ (pctermLocallyClosedRec env <$> args1)
  sequence_ (pctermLocallyClosedRec env <$> args2)
termLocallyClosedRec env (Case _ _ e cases) = do
  termLocallyClosedRec env e
  sequence_ (termCaseLocallyClosedRec env <$> cases)
termLocallyClosedRec env (Cocase _ _ cases) =
  sequence_ (termCaseILocallyClosedRec env <$> cases)
termLocallyClosedRec _ (PrimLitI64 _ _) = Right ()
termLocallyClosedRec _ (PrimLitF64 _ _) = Right ()

termCaseLocallyClosedRec :: [[(PrdCns,())]] -> TermCase ext -> Either Error ()
termCaseLocallyClosedRec env (MkTermCase _ _ args e) = do
  termLocallyClosedRec (((\(x,_) -> (x,())) <$> args):env) e

termCaseILocallyClosedRec :: [[(PrdCns,())]] -> TermCaseI ext -> Either Error ()
termCaseILocallyClosedRec env (MkTermCaseI _ _ (as1, (), as2) e) =
  let newArgs = (\(x,_) -> (x,())) <$> as1 ++ [(Cns, Nothing)] ++ as2 in
  termLocallyClosedRec (newArgs:env) e

commandLocallyClosedRec :: [[(PrdCns,())]] -> Command ext -> Either Error ()
commandLocallyClosedRec _ (ExitSuccess _) = Right ()
commandLocallyClosedRec _ (ExitFailure _) = Right ()
commandLocallyClosedRec _ (Jump _ _) = Right ()
commandLocallyClosedRec env (Print _ t cmd) = termLocallyClosedRec env t >> commandLocallyClosedRec env cmd
commandLocallyClosedRec env (Read _ cns) = termLocallyClosedRec env cns
commandLocallyClosedRec env (Apply _ _ t1 t2) = termLocallyClosedRec env t1 >> termLocallyClosedRec env t2
commandLocallyClosedRec env (PrimOp _ _ _ subst) = sequence_ $ pctermLocallyClosedRec env <$> subst

termLocallyClosed :: Term pc ext -> Either Error ()
termLocallyClosed = termLocallyClosedRec []

commandLocallyClosed :: Command ext -> Either Error ()
commandLocallyClosed = commandLocallyClosedRec []

---------------------------------------------------------------------------------
-- These functions  translate a locally nameless term into a named representation.
--
-- Use only for prettyprinting! These functions only "undo" the steps in the parser
-- and do not fulfil any semantic properties w.r.t shadowing etc.!
---------------------------------------------------------------------------------

freeVarNamesToXtorArgs :: [(PrdCns, Maybe FreeVarName)] -> Substitution Compiled
freeVarNamesToXtorArgs bs = f <$> bs
  where
    f (Prd, Nothing) = error "Create Names first!"
    f (Prd, Just fv) = PrdTerm $ FreeVar () PrdRep fv
    f (Cns, Nothing) = error "Create Names first!"
    f (Cns, Just fv) = CnsTerm $ FreeVar () CnsRep fv

openTermCase :: TermCase ext -> TermCase Compiled
openTermCase MkTermCase { tmcase_name, tmcase_args, tmcase_term } =
    MkTermCase { tmcase_ext = ()
               , tmcase_name = tmcase_name
               , tmcase_args = tmcase_args
               , tmcase_term = termOpening (freeVarNamesToXtorArgs tmcase_args) (openTermComplete tmcase_term)
               }

openTermCaseI :: TermCaseI ext -> TermCaseI Compiled
openTermCaseI MkTermCaseI { tmcasei_name, tmcasei_args = (as1, (), as2), tmcasei_term } =

  MkTermCaseI { tmcasei_ext = ()
              , tmcasei_name = tmcasei_name
              , tmcasei_args = (as1, (), as2)
              , tmcasei_term = termOpening (freeVarNamesToXtorArgs (as1 ++ [(Cns, Nothing)] ++ as2)) (openTermComplete tmcasei_term)
              }

openCmdCase :: CmdCase ext -> CmdCase Compiled
openCmdCase MkCmdCase { cmdcase_name, cmdcase_args, cmdcase_cmd } =
  MkCmdCase { cmdcase_ext = ()
            , cmdcase_name = cmdcase_name
            , cmdcase_args = cmdcase_args
            , cmdcase_cmd = commandOpening (freeVarNamesToXtorArgs cmdcase_args) (openCommandComplete cmdcase_cmd)
            }

openPCTermComplete :: PrdCnsTerm ext -> PrdCnsTerm Compiled
openPCTermComplete (PrdTerm tm) = PrdTerm $ openTermComplete tm
openPCTermComplete (CnsTerm tm) = CnsTerm $ openTermComplete tm

openTermComplete :: Term pc ext -> Term pc Compiled
openTermComplete (BoundVar _ pc idx) = BoundVar () pc idx
openTermComplete (FreeVar _ pc v) = FreeVar () pc v
openTermComplete (Xtor _ pc ns xt args) = Xtor () pc ns xt (openPCTermComplete <$> args)
openTermComplete (XMatch _ pc ns cases) = XMatch () pc ns (openCmdCase <$> cases)
openTermComplete (MuAbs _ PrdRep (Just fv) cmd) =
  MuAbs () PrdRep (Just fv) (commandOpening [CnsTerm (FreeVar () CnsRep fv)] (openCommandComplete cmd))
openTermComplete (MuAbs _ PrdRep Nothing _) = error "Create names first!"
openTermComplete (MuAbs _ CnsRep (Just fv) cmd) =
  MuAbs () CnsRep (Just fv) (commandOpening [PrdTerm (FreeVar () PrdRep fv)] (openCommandComplete cmd))
openTermComplete (MuAbs _ CnsRep Nothing _) = error "Create names first!"
openTermComplete (Dtor _ ns xt t (args1,pcrep,args2)) =
  Dtor () ns xt (openTermComplete t) (openPCTermComplete <$> args1,pcrep, openPCTermComplete <$> args2)
openTermComplete (Case _ ns t cases) = Case () ns (openTermComplete t) (openTermCase <$> cases)
openTermComplete (Cocase _ ns cocases) = Cocase () ns (openTermCaseI <$> cocases)
openTermComplete (PrimLitI64 _ i) = PrimLitI64 () i
openTermComplete (PrimLitF64 _ d) = PrimLitF64 () d

openCommandComplete :: Command ext -> Command Compiled
openCommandComplete (Apply _ kind t1 t2) = Apply () kind (openTermComplete t1) (openTermComplete t2)
openCommandComplete (Print _ t cmd) = Print () (openTermComplete t) (openCommandComplete cmd)
openCommandComplete (Read _ cns) = Read () (openTermComplete cns)
openCommandComplete (Jump _ fv) = Jump () fv
openCommandComplete (ExitSuccess _) = ExitSuccess ()
openCommandComplete (ExitFailure _) = ExitFailure ()
openCommandComplete (PrimOp _ pt op subst) = PrimOp () pt op (openPCTermComplete <$> subst)

---------------------------------------------------------------------------------
-- Shifting
--
-- Used in program transformations like focusing.
---------------------------------------------------------------------------------

shiftPCTermRec :: Int -> PrdCnsTerm ext -> PrdCnsTerm ext
shiftPCTermRec n (PrdTerm tm) = PrdTerm $ shiftTermRec n tm
shiftPCTermRec n (CnsTerm tm) = CnsTerm $ shiftTermRec n tm

shiftTermRec :: Int -> Term pc ext -> Term pc ext
shiftTermRec _ var@FreeVar {} = var
shiftTermRec n (BoundVar ext pcrep (i,j)) | n <= i    = BoundVar ext pcrep (i + 1, j)
                                          | otherwise = BoundVar ext pcrep (i    , j)
shiftTermRec n (Xtor ext pcrep ns xt subst) =
    Xtor ext pcrep ns xt (shiftPCTermRec n <$> subst)
shiftTermRec n (XMatch ext pcrep ns cases) = XMatch ext pcrep ns (shiftCmdCaseRec (n + 1) <$> cases)
shiftTermRec n (MuAbs ext pcrep bs cmd) = MuAbs ext pcrep bs (shiftCmdRec (n + 1) cmd)
shiftTermRec n (Dtor ext ns xt e (args1,pcrep,args2)) =
  Dtor ext ns xt (shiftTermRec n e) (shiftPCTermRec n <$> args1,pcrep,shiftPCTermRec n <$> args2)
shiftTermRec n (Case ext ns e cases) = Case ext ns (shiftTermRec n e) (shiftTermCaseRec n <$> cases)
shiftTermRec n (Cocase ext ns cases) = Cocase ext ns (shiftTermCaseIRec n <$> cases)
shiftTermRec _ lit@PrimLitI64{} = lit
shiftTermRec _ lit@PrimLitF64{} = lit

shiftTermCaseRec :: Int -> TermCase ext -> TermCase ext
shiftTermCaseRec n (MkTermCase ext xt args e) = MkTermCase ext xt args (shiftTermRec n e)

shiftTermCaseIRec :: Int -> TermCaseI ext -> TermCaseI ext
shiftTermCaseIRec n (MkTermCaseI ext xt args e) = MkTermCaseI ext xt args (shiftTermRec n e)

shiftCmdCaseRec :: Int -> CmdCase ext-> CmdCase ext
shiftCmdCaseRec n (MkCmdCase ext name bs cmd) = MkCmdCase ext name bs (shiftCmdRec n cmd)

shiftCmdRec :: Int -> Command ext -> Command ext
shiftCmdRec n (Apply ext kind prd cns) = Apply ext kind (shiftTermRec n prd) (shiftTermRec n cns)
shiftCmdRec _ (ExitSuccess ext) = ExitSuccess ext
shiftCmdRec _ (ExitFailure ext) = ExitFailure ext
shiftCmdRec n (Print ext prd cmd) = Print ext (shiftTermRec n prd) (shiftCmdRec n cmd)
shiftCmdRec n (Read ext cns) = Read ext (shiftTermRec n cns)
shiftCmdRec _ (Jump ext fv) = Jump ext fv
shiftCmdRec n (PrimOp ext pt op subst) = PrimOp ext pt op (shiftPCTermRec n <$> subst)

-- | Shift all unbound BoundVars up by one.
shiftTerm :: Term pc ext -> Term pc ext
shiftTerm = shiftTermRec 0

-- | Shift all unbound BoundVars up by one.
shiftCmd :: Command ext -> Command ext
shiftCmd = shiftCmdRec 0

---------------------------------------------------------------------------------
-- Remove Names
--
-- Replaces all variable binding sites with Nothing
---------------------------------------------------------------------------------

removeNamesPrdCnsTerm :: PrdCnsTerm ext -> PrdCnsTerm ext
removeNamesPrdCnsTerm (PrdTerm tm) = PrdTerm $ removeNamesTerm tm
removeNamesPrdCnsTerm (CnsTerm tm) = CnsTerm $ removeNamesTerm tm

removeNamesTerm :: Term pc  ext -> Term pc ext
removeNamesTerm f@FreeVar{} = f
removeNamesTerm f@BoundVar{} = f
removeNamesTerm (Xtor ext pc ns xt args) = Xtor ext pc ns xt (removeNamesPrdCnsTerm <$> args)
removeNamesTerm (MuAbs ext pc _ cmd) = MuAbs ext pc Nothing (removeNamesCmd cmd)
removeNamesTerm (XMatch ext pc ns cases) = XMatch ext pc ns (removeNamesCmdCase <$> cases)
removeNamesTerm (Dtor ext ns xt e (args1,pcrep,args2)) =
  Dtor ext ns xt (removeNamesTerm e) (removeNamesPrdCnsTerm <$> args1,pcrep,removeNamesPrdCnsTerm <$> args2)
removeNamesTerm (Case ext ns e cases) = Case ext ns (removeNamesTerm e) (removeNamesTermCase <$> cases)
removeNamesTerm (Cocase ext ns cases) = Cocase ext ns (removeNamesTermCaseI <$> cases)
removeNamesTerm lit@PrimLitI64{} = lit
removeNamesTerm lit@PrimLitF64{} = lit

removeNamesTermCase :: TermCase ext -> TermCase ext
removeNamesTermCase (MkTermCase ext xt args e)   = MkTermCase ext xt ((\(pc,_) -> (pc,Nothing)) <$> args) (removeNamesTerm e)

removeNamesTermCaseI :: TermCaseI ext -> TermCaseI ext
removeNamesTermCaseI (MkTermCaseI ext xt (as1, (), as2) e) =
  let r = \(pc,_) -> (pc, Nothing) in
  MkTermCaseI ext xt (r <$> as1, (), r <$> as2) (removeNamesTerm e)

removeNamesCmdCase :: CmdCase ext -> CmdCase ext
removeNamesCmdCase (MkCmdCase ext xt args cmd) = MkCmdCase ext xt ((\(pc,_) -> (pc,Nothing)) <$> args) (removeNamesCmd cmd)

removeNamesCmd :: Command ext -> Command ext
removeNamesCmd (Apply ext kind prd cns) = Apply ext kind (removeNamesTerm prd) (removeNamesTerm cns)
removeNamesCmd (Print ext prd cmd) = Print ext (removeNamesTerm prd) (removeNamesCmd cmd)
removeNamesCmd (Read ext cns) = Read ext (removeNamesTerm cns)
removeNamesCmd (Jump ext fv) = Jump ext fv
removeNamesCmd (ExitSuccess ext) = ExitSuccess ext
removeNamesCmd (ExitFailure ext) = ExitFailure ext
removeNamesCmd (PrimOp ext pt op subst) = PrimOp ext pt op (removeNamesPrdCnsTerm <$> subst)
