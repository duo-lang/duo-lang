module Syntax.Terms where

import Data.Kind (Type)
import Data.List (elemIndex)
import Data.Maybe (fromJust, isJust)
import Data.Text qualified as T

import Utils
import Errors
import Syntax.CommonTerm
    ( Index,
      FreeVarName,
      XtorName,
      NominalStructural,
      PrdCnsRep(..),
      PrdCns(..),
      Phase(..) )
import Syntax.Types

---------------------------------------------------------------------------------
-- Variable representation
--
-- We use the locally nameless representation for terms, which combines names for
-- free variables with  anonymous deBruijn indexes for bound variables.
-- The locally namelesss representation is well documented here:
-- https://www.chargueraud.org/softs/ln/
---------------------------------------------------------------------------------

---------------------------------------------------------------------------------
-- Substitution
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

type Substitution ext = [PrdCnsTerm ext]

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
--        |  acase_args  acase_term
--        |
--    acase_name
--
data ACase (ext :: Phase) = MkACase
  { acase_ext  :: CaseExt ext
  , acase_name :: XtorName
  , acase_args :: [(PrdCns, Maybe FreeVarName)]
  , acase_term :: Term Prd ext
  }

deriving instance (Eq (ACase Parsed))
deriving instance (Eq (ACase Inferred))
deriving instance (Eq (ACase Compiled))
deriving instance (Show (ACase Parsed))
deriving instance (Show (ACase Inferred))
deriving instance (Show (ACase Compiled))

-- | Represents one case in a pattern match or copattern match.
--
--        X(x_1,...,x_n)[k_1,...,k_m] => c
--        ^ ^^^^^^^^^^^^^^^^^^^^^^^^     ^
--        |              |               |
--    scase_name     scase_args      scase_cmd
--
data SCase (ext :: Phase) = MkSCase
  { scase_ext  :: CaseExt ext
  , scase_name :: XtorName
  , scase_args :: [(PrdCns, Maybe FreeVarName)]
  , scase_cmd  :: Command ext
  }

deriving instance (Eq (SCase Parsed))
deriving instance (Eq (SCase Inferred))
deriving instance (Eq (SCase Compiled))
deriving instance (Show (SCase Parsed))
deriving instance (Show (SCase Inferred))
deriving instance (Show (SCase Compiled))

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
  XtorCall :: TermExt pc ext -> PrdCnsRep pc -> XtorName -> Substitution ext -> Term pc ext
  -- | A pattern or copattern match.
  -- If the first argument is `PrdRep` it is a copattern match, a pattern match otherwise.
  XMatch :: TermExt pc ext -> PrdCnsRep pc -> NominalStructural -> [SCase ext] -> Term pc ext
  -- | A Mu or TildeMu abstraction:
  --
  --  mu k.c    =   MuAbs PrdRep c
  -- ~mu x.c    =   MuAbs CnsRep c
  MuAbs :: TermExt pc ext -> PrdCnsRep pc -> Maybe FreeVarName -> Command ext -> Term pc ext
  --
  -- Syntactic Sugar
  --
  Dtor :: TermExt Prd ext -> XtorName -> Term Prd ext -> Substitution ext -> Term Prd ext
  -- | A pattern match:
  --
  -- case e of { ... }
  --
  Match :: TermExt Prd ext -> NominalStructural -> Term Prd ext -> [ACase ext] -> Term Prd ext
  -- | A copattern match:
  --
  -- cocase { ... }
  --
  Comatch :: TermExt Prd ext -> NominalStructural -> [ACase ext] -> Term Prd ext



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
getTypeTerm (XtorCall ext rep _ _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeTerm (XMatch   ext rep _ _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeTerm (MuAbs    ext rep _ _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeTerm (Dtor (_,ty) _ _ _) = ty
getTypeTerm (Match (_,ty) _ _ _)  = ty
getTypeTerm (Comatch (_,ty) _ _)  = ty

getTypArgs :: Substitution Inferred -> LinearContext Pos
getTypArgs subst = getTypArgs' <$> subst
  where
    getTypArgs' (PrdTerm tm) = PrdType $ getTypeTerm tm
    getTypArgs' (CnsTerm tm) = CnsType $ getTypeTerm tm


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
  Apply :: CommandExt ext -> Term Prd ext -> Term Cns ext -> Command ext
  Print :: CommandExt ext -> Term Prd ext -> Command ext
  Done  :: CommandExt ext -> Command ext

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
termOpeningRec k args (XtorCall _ s xt subst) =
  XtorCall () s xt (pctermOpeningRec k args <$> subst)
termOpeningRec k args (XMatch _ pc sn cases) =
  XMatch () pc sn $ map (\pmcase@MkSCase{ scase_cmd } -> pmcase { scase_cmd = commandOpeningRec (k+1) args scase_cmd }) cases
termOpeningRec k args (MuAbs _ pc a cmd) =
  MuAbs () pc a (commandOpeningRec (k+1) args cmd)
-- ATerms
termOpeningRec k args (Dtor _ xt t args') =
  Dtor () xt (termOpeningRec k args t) (pctermOpeningRec k args <$> args')
termOpeningRec k args (Match _ ns t cases) =
  Match () ns (termOpeningRec k args t) ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = termOpeningRec (k + 1) args acase_term }) <$> cases)
termOpeningRec k args (Comatch _ ns cocases) =
  Comatch () ns ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = termOpeningRec (k + 1) args acase_term }) <$> cocases)



commandOpeningRec :: Int -> Substitution Compiled -> Command Compiled -> Command Compiled
commandOpeningRec _ _ (Done _) = Done ()
commandOpeningRec k args (Print _ t) = Print () (termOpeningRec k args t)
commandOpeningRec k args (Apply _ t1 t2) = Apply () (termOpeningRec k args t1) (termOpeningRec k args t2)

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
termClosingRec k vars (XtorCall ext s xt subst) =
  XtorCall ext s xt (pctermClosingRec k vars <$> subst)
termClosingRec k vars (XMatch ext pc sn cases) =
  XMatch ext pc sn $ map (\pmcase@MkSCase { scase_cmd } -> pmcase { scase_cmd = commandClosingRec (k+1) vars scase_cmd }) cases
termClosingRec k vars (MuAbs ext pc a cmd) =
  MuAbs ext pc a (commandClosingRec (k+1) vars cmd)
-- ATerms
termClosingRec k args (Dtor ext xt t args') =
  Dtor ext xt (termClosingRec k args t) (pctermClosingRec k args <$> args')
termClosingRec k args (Match ext ns t cases) =
  Match ext ns (termClosingRec k args t) ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = termClosingRec (k + 1) args acase_term }) <$> cases)
termClosingRec k args (Comatch ext ns cocases) =
  Comatch ext ns ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = termClosingRec (k + 1) args acase_term }) <$> cocases)

commandClosingRec :: Int -> [(PrdCns, FreeVarName)] -> Command ext -> Command ext
commandClosingRec _ _ (Done ext) = Done ext
commandClosingRec k args (Print ext t) = Print ext (termClosingRec k args t)
commandClosingRec k args (Apply ext t1 t2) = Apply ext (termClosingRec k args t1) (termClosingRec k args t2)

termClosing :: [(PrdCns, FreeVarName)] -> Term pc ext -> Term pc ext
termClosing = termClosingRec 0

commandClosing :: [(PrdCns, FreeVarName)] -> Command ext -> Command ext
commandClosing = commandClosingRec 0

---------------------------------------------------------------------------------
-- Check for locally closedness
---------------------------------------------------------------------------------

checkIfBound :: [[(PrdCns,a)]] -> PrdCnsRep pc -> Index -> Either Error ()
checkIfBound env rep  (i, j) | i >= length env = Left $ OtherError $ "Variable " <> T.pack (show (i,j)) <> " is not bound (Outer index)"
                             | otherwise = checkIfBoundInner (env !! i) rep (i,j)

checkIfBoundInner :: [(PrdCns,a)] -> PrdCnsRep pc -> Index -> Either Error ()
checkIfBoundInner vars PrdRep idx@(_,j) =
  if j < length vars
    then case vars !! j of
      (Prd,_) -> return ()
      (Cns,_) -> Left $ OtherError $ "Variable " <> T.pack (show idx) <> " is not bound to Producer"
    else Left $ OtherError $ "Variable " <> T.pack (show idx) <> " is not bound (Inner index)"
checkIfBoundInner vars CnsRep idx@(_,j) =
  if j < length vars
    then case vars !! j of
      (Cns,_) -> return ()
      (Prd,_) -> Left $ OtherError $ "Variable " <> T.pack (show idx) <> " is not bound to Consumer"
    else Left $ OtherError $ "Variable " <> T.pack (show idx) <> " is not bound (Inner index)"

pctermLocallyClosedRec :: [[(PrdCns, ())]] -> PrdCnsTerm ext -> Either Error ()
pctermLocallyClosedRec env (PrdTerm tm) = termLocallyClosedRec env tm
pctermLocallyClosedRec env (CnsTerm tm) = termLocallyClosedRec env tm

termLocallyClosedRec :: [[(PrdCns,())]] -> Term pc ext -> Either Error ()
termLocallyClosedRec env (BoundVar _ pc idx) = checkIfBound env pc idx
termLocallyClosedRec _ (FreeVar _ _ _) = Right ()
termLocallyClosedRec env (XtorCall _ _ _ subst) = do
  sequence_ (pctermLocallyClosedRec env <$> subst)
termLocallyClosedRec env (XMatch _ _ _ cases) = do
  sequence_ ((\MkSCase { scase_cmd, scase_args } -> commandLocallyClosedRec (((\(x,_) -> (x,())) <$> scase_args) : env) scase_cmd) <$> cases)
termLocallyClosedRec env (MuAbs _ PrdRep _ cmd) = commandLocallyClosedRec ([(Cns,())] : env) cmd
termLocallyClosedRec env (MuAbs _ CnsRep _ cmd) = commandLocallyClosedRec ([(Prd,())] : env) cmd
termLocallyClosedRec env (Dtor _ _ e args) = do
  termLocallyClosedRec env e
  sequence_ (pctermLocallyClosedRec env <$> args)
termLocallyClosedRec env (Match _ _ e cases) = do
  termLocallyClosedRec env e
  sequence_ (acaseLocallyClosedRec env <$> cases)
termLocallyClosedRec env (Comatch _ _ cases) =
  sequence_ (acaseLocallyClosedRec env <$> cases)

acaseLocallyClosedRec :: [[(PrdCns,())]] -> ACase ext -> Either Error ()
acaseLocallyClosedRec env (MkACase _ _ args e) = do
  termLocallyClosedRec ((((\(x,_) -> (x,())) <$> args)):env) e

commandLocallyClosedRec :: [[(PrdCns,())]] -> Command ext -> Either Error ()
commandLocallyClosedRec _ (Done _) = Right ()
commandLocallyClosedRec env (Print _ t) = termLocallyClosedRec env t
commandLocallyClosedRec env (Apply _ t1 t2) = termLocallyClosedRec env t1 >> termLocallyClosedRec env t2

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

openACase :: ACase ext -> ACase Compiled
openACase MkACase { acase_name, acase_args, acase_term } =
    MkACase { acase_ext = ()
            , acase_name = acase_name
            , acase_args = acase_args
            , acase_term = termOpening (freeVarNamesToXtorArgs acase_args) (openTermComplete acase_term)
            }

openSCase :: SCase ext -> SCase Compiled
openSCase MkSCase { scase_name, scase_args, scase_cmd } =
  MkSCase { scase_ext = ()
          , scase_name = scase_name
          , scase_args = scase_args
          , scase_cmd = commandOpening (freeVarNamesToXtorArgs scase_args) (openCommandComplete scase_cmd)
          }

openPCTermComplete :: PrdCnsTerm ext -> PrdCnsTerm Compiled
openPCTermComplete (PrdTerm tm) = PrdTerm $ openTermComplete tm
openPCTermComplete (CnsTerm tm) = CnsTerm $ openTermComplete tm

openTermComplete :: Term pc ext -> Term pc Compiled
openTermComplete (BoundVar _ pc idx) = BoundVar () pc idx
openTermComplete (FreeVar _ pc v) = FreeVar () pc v
openTermComplete (XtorCall _ pc name args) = XtorCall () pc name (openPCTermComplete <$> args)
openTermComplete (XMatch _ pc ns cases) = XMatch () pc ns (openSCase <$> cases)
openTermComplete (MuAbs _ PrdRep (Just fv) cmd) =
  MuAbs () PrdRep (Just fv) (commandOpening [CnsTerm (FreeVar () CnsRep fv)] (openCommandComplete cmd))
openTermComplete (MuAbs _ PrdRep Nothing _) = error "Create names first!"
openTermComplete (MuAbs _ CnsRep (Just fv) cmd) =
  MuAbs () CnsRep (Just fv) (commandOpening [PrdTerm (FreeVar () PrdRep fv)] (openCommandComplete cmd))
openTermComplete (MuAbs _ CnsRep Nothing _) = error "Create names first!"
openTermComplete (Dtor _ name t args) = Dtor () name (openTermComplete t) (openPCTermComplete <$> args)
openTermComplete (Match _ ns t cases) = Match () ns (openTermComplete t) (openACase <$> cases)
openTermComplete (Comatch _ ns cocases) = Comatch () ns (openACase <$> cocases)

openCommandComplete :: Command ext -> Command Compiled
openCommandComplete (Apply _ t1 t2) = Apply () (openTermComplete t1) (openTermComplete t2)
openCommandComplete (Print _ t) = Print () (openTermComplete t)
openCommandComplete (Done _) = Done ()


---------------------------------------------------------------------------------
-- Shifting
--
-- Used in program transformations like focusing.
---------------------------------------------------------------------------------

shiftPCTerm :: Int -> PrdCnsTerm ext -> PrdCnsTerm ext
shiftPCTerm n (PrdTerm tm) = PrdTerm $ shiftTerm' n tm
shiftPCTerm n (CnsTerm tm) = CnsTerm $ shiftTerm' n tm

shiftTerm' :: Int -> Term pc ext -> Term pc ext
shiftTerm' _ var@FreeVar {} = var
shiftTerm' n (BoundVar ext pcrep (i,j)) | n <= i    = BoundVar ext pcrep (i + 1, j)
                                         | otherwise = BoundVar ext pcrep (i    , j)
shiftTerm' n (XtorCall ext pcrep name subst) =
    XtorCall ext pcrep name (shiftPCTerm n <$> subst)
shiftTerm' n (XMatch ext pcrep ns cases) = XMatch ext pcrep ns (shiftSCase (n + 1) <$> cases)
shiftTerm' n (MuAbs ext pcrep bs cmd) = MuAbs ext pcrep bs (shiftCmd' (n + 1) cmd)
shiftTerm' n (Dtor ext xt e args) = Dtor ext xt (shiftTerm' n e) (shiftPCTerm n <$> args)
shiftTerm' n (Match ext ns e cases) = Match ext ns (shiftTerm' n e) (shiftACase n <$> cases)
shiftTerm' n (Comatch ext ns cases) = Comatch ext ns (shiftACase n <$> cases)

shiftACase :: Int -> ACase ext -> ACase ext
shiftACase n (MkACase ext xt args e) = MkACase ext xt args (shiftTerm' n e)

shiftSCase :: Int -> SCase ext-> SCase ext
shiftSCase n (MkSCase ext name bs cmd) = MkSCase ext name bs (shiftCmd' n cmd)

shiftCmd' :: Int -> Command ext -> Command ext
shiftCmd' n (Apply ext prd cns) = Apply ext (shiftTerm' n prd) (shiftTerm' n cns)
shiftCmd' _ (Done ext) = Done ext
shiftCmd' n (Print ext prd) = Print ext (shiftTerm' n prd)

-- | Shift all unbound BoundVars up by one.
shiftTerm :: Term pc ext -> Term pc ext
shiftTerm = shiftTerm' 0

-- | Shift all unbound BoundVars up by one.
shiftCmd :: Command ext -> Command ext
shiftCmd = shiftCmd' 0

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
removeNamesTerm (XtorCall ext pc xt args) = XtorCall ext pc xt (removeNamesPrdCnsTerm <$> args)
removeNamesTerm (MuAbs ext pc _ cmd) = MuAbs ext pc Nothing (removeNamesCmd cmd)
removeNamesTerm (XMatch ext pc ns cases) = XMatch ext pc ns (removeNamesSCase <$> cases)
removeNamesTerm (Dtor ext xt e args) = Dtor ext xt (removeNamesTerm e) (removeNamesPrdCnsTerm <$> args)
removeNamesTerm (Match ext ns e cases) = Match ext ns (removeNamesTerm e) (removeNamesACase <$> cases)
removeNamesTerm (Comatch ext ns cases) = Comatch ext ns (removeNamesACase <$> cases)

removeNamesACase :: ACase ext -> ACase ext
removeNamesACase (MkACase ext xt args e)   = MkACase ext xt ((\(pc,_) -> (pc,Nothing)) <$> args) (removeNamesTerm e)

removeNamesSCase :: SCase ext -> SCase ext
removeNamesSCase (MkSCase ext xt args cmd) = MkSCase ext xt ((\(pc,_) -> (pc,Nothing)) <$> args) (removeNamesCmd cmd)

removeNamesCmd :: Command ext -> Command ext
removeNamesCmd (Apply ext prd cns) = Apply ext (removeNamesTerm prd) (removeNamesTerm cns)
removeNamesCmd (Print ext prd) = Print ext (removeNamesTerm prd)
removeNamesCmd (Done ext) = Done ext
