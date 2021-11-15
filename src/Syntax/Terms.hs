module Syntax.Terms where

import Control.Monad.State

import Data.Bifunctor
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
      Phase(..),
      flipPrdCns )
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

{-# DEPRECATED oldToNewSubst "Deprecated" #-}
oldToNewSubst :: ([Term Prd ext],[Term Cns ext]) -> Substitution ext
oldToNewSubst (prdArgs, cnsArgs) = (PrdTerm <$> prdArgs) ++ (CnsTerm <$> cnsArgs)

{-# DEPRECATED newToOldSubst "Deprecated" #-}
newToOldSubst :: Substitution ext -> ([Term Prd ext],[Term Cns ext])
newToOldSubst subst = foo subst ([],[])
  where
    foo :: Substitution ext -> ([Term Prd ext],[Term Cns ext]) -> ([Term Prd ext],[Term Cns ext])
    foo [] res = res
    foo (PrdTerm tm:rest) (prdArgs,cnsArgs) = foo rest (tm : prdArgs, cnsArgs)
    foo (CnsTerm tm:rest) (prdArgs,cnsArgs) = foo rest (prdArgs, tm : cnsArgs)

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
  , acase_args :: [Maybe FreeVarName]
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
  , scase_args :: Twice [Maybe FreeVarName]
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
  TermExt Prd Inferred = (Loc, Typ Pos)
  TermExt Cns Inferred = (Loc, Typ Neg)
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
  -- Asymmetric Terms!
  --
  Dtor :: TermExt Prd ext -> XtorName -> Term Prd ext -> [Term Prd ext] -> Term Prd ext
  -- | A pattern match:
  --
  -- match e with { ... }
  --
  Match :: TermExt Prd ext -> Term Prd ext -> [ACase ext] -> Term Prd ext
  -- | A copattern match:
  --
  -- comatch { ... }
  --
  Comatch :: TermExt Prd ext -> [ACase ext] -> Term Prd ext



deriving instance (Eq (Term pc Parsed))
deriving instance (Eq (Term Prd Inferred))
deriving instance (Eq (Term Cns Inferred))
deriving instance (Eq (Term pc Compiled))
deriving instance (Show (Term pc Parsed))
deriving instance (Show (Term Prd Inferred))
deriving instance (Show (Term Cns Inferred))
deriving instance (Show (Term pc Compiled))

getTypeSTerm :: Term pc Inferred -> Typ (PrdCnsToPol pc)
getTypeSTerm (BoundVar ext rep _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeSTerm (FreeVar  ext rep _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeSTerm (XtorCall ext rep _ _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeSTerm (XMatch   ext rep _ _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeSTerm (MuAbs    ext rep _ _)  = case rep of
  PrdRep -> case ext of (_,ty) -> ty
  CnsRep -> case ext of (_,ty) -> ty
getTypeSTerm (Dtor (_,ty) _ _ _) = ty
getTypeSTerm (Match (_,ty) _ _)  = ty
getTypeSTerm (Comatch (_,ty) _)  = ty

getTypArgs :: Substitution Inferred -> TypArgs Pos
getTypArgs subst = MkTypArgs (getTypeSTerm <$> prdArgs) (getTypeSTerm <$> cnsArgs)
  where
    (prdArgs, cnsArgs) = newToOldSubst subst

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
termOpeningRec k subst bv@(BoundVar _ PrdRep (i,j)) | i == k    = let (prdArgs,_) = newToOldSubst subst in prdArgs !! j
                                                                | otherwise = bv
termOpeningRec k subst bv@(BoundVar _ CnsRep (i,j)) | i == k    = let (_,cnsArgs) = newToOldSubst subst in cnsArgs !! j
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
  Dtor () xt (termOpeningRec k args t) (termOpeningRec k args <$> args')
termOpeningRec k args (Match _ t cases) =
  Match () (termOpeningRec k args t) ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = termOpeningRec (k + 1) args acase_term }) <$> cases)
termOpeningRec k args (Comatch _ cocases) =
  Comatch () ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = termOpeningRec (k + 1) args acase_term }) <$> cocases)

termOpening :: Substitution Compiled -> Term pc Compiled -> Term pc Compiled
termOpening = termOpeningRec 0

commandOpeningRec :: Int -> Substitution Compiled -> Command Compiled -> Command Compiled
commandOpeningRec _ _ (Done _) = Done ()
commandOpeningRec k args (Print _ t) = Print () (termOpeningRec k args t)
commandOpeningRec k args (Apply _ t1 t2) = Apply () (termOpeningRec k args t1) (termOpeningRec k args t2)


-- replaces bound variables pointing "outside" of a command with given arguments
commandOpening :: Substitution Compiled -> Command Compiled -> Command Compiled
commandOpening = commandOpeningRec 0

commandOpeningSingle :: PrdCnsRep pc -> Term pc Compiled -> Command Compiled -> Command Compiled
commandOpeningSingle PrdRep t = commandOpening [PrdTerm t]
commandOpeningSingle CnsRep t = commandOpening [CnsTerm t]

---------------------------------------------------------------------------------
-- Variable Closing
---------------------------------------------------------------------------------

pctermClosingRec :: Int -> Twice [FreeVarName] -> PrdCnsTerm ext -> PrdCnsTerm ext
pctermClosingRec k vars (PrdTerm tm) = PrdTerm $ termClosingRec k vars tm
pctermClosingRec k vars (CnsTerm tm) = CnsTerm $ termClosingRec k vars tm

termClosingRec :: Int -> Twice [FreeVarName] -> Term pc ext -> Term pc ext
termClosingRec _ _ bv@(BoundVar _ _ _) = bv
termClosingRec k (Twice prdvars _) (FreeVar ext PrdRep v) | isJust (v `elemIndex` prdvars) = BoundVar ext PrdRep (k, fromJust (v `elemIndex` prdvars))
                                                          | otherwise = FreeVar ext PrdRep v
termClosingRec k (Twice _ cnsvars) (FreeVar ext CnsRep v) | isJust (v `elemIndex` cnsvars) = BoundVar ext CnsRep (k, fromJust (v `elemIndex` cnsvars))
                                                          | otherwise = FreeVar ext CnsRep v
termClosingRec k vars (XtorCall ext s xt subst) =
  XtorCall ext s xt (pctermClosingRec k vars <$> subst)
termClosingRec k vars (XMatch ext pc sn cases) =
  XMatch ext pc sn $ map (\pmcase@MkSCase { scase_cmd } -> pmcase { scase_cmd = commandClosingRec (k+1) vars scase_cmd }) cases
termClosingRec k vars (MuAbs ext pc a cmd) =
  MuAbs ext pc a (commandClosingRec (k+1) vars cmd)
-- ATerms
termClosingRec k args (Dtor ext xt t args') =
  Dtor ext xt (termClosingRec k args t) (termClosingRec k args <$> args')
termClosingRec k args (Match ext t cases) =
  Match ext (termClosingRec k args t) ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = termClosingRec (k + 1) args acase_term }) <$> cases)
termClosingRec k args (Comatch ext cocases) =
  Comatch ext ((\pmcase@MkACase { acase_term } -> pmcase { acase_term = termClosingRec (k + 1) args acase_term }) <$> cocases)

commandClosingRec :: Int -> Twice [FreeVarName] -> Command ext -> Command ext
commandClosingRec _ _ (Done ext) = Done ext
commandClosingRec k args (Print ext t) = Print ext (termClosingRec k args t)
commandClosingRec k args (Apply ext t1 t2) = Apply ext (termClosingRec k args t1) (termClosingRec k args t2)

termClosing :: Twice [FreeVarName] -> Term pc ext -> Term pc ext
termClosing = termClosingRec 0

commandClosing :: Twice [FreeVarName] -> Command ext -> Command ext
commandClosing = commandClosingRec 0

commandClosingSingle :: PrdCnsRep pc -> FreeVarName -> Command ext -> Command ext
commandClosingSingle PrdRep v = commandClosing (Twice [v] [])
commandClosingSingle CnsRep v = commandClosing (Twice [] [v])


---------------------------------------------------------------------------------
-- Check for locally closedness
---------------------------------------------------------------------------------

checkIfBound :: [Twice [a]] -> PrdCnsRep pc -> Index -> Either Error ()
checkIfBound env rep  (i, j) | i >= length env = Left $ OtherError "Variable is not bound"
                             | otherwise = checkIfBound' (env !! i) rep j

checkIfBound' :: Twice [a] -> PrdCnsRep pc -> Int -> Either Error ()
checkIfBound' (Twice prds _) PrdRep j = if j < length prds then Right () else Left $ OtherError "Variable is not bound"
checkIfBound' (Twice _ cnss) CnsRep j = if j < length cnss then Right () else Left $ OtherError "Variable is not bound"

pctermLocallyClosedRec :: [Twice [()]] -> PrdCnsTerm ext -> Either Error ()
pctermLocallyClosedRec env (PrdTerm tm) = termLocallyClosedRec env tm
pctermLocallyClosedRec env (CnsTerm tm) = termLocallyClosedRec env tm

termLocallyClosedRec :: [Twice [()]] -> Term pc ext -> Either Error ()
termLocallyClosedRec env (BoundVar _ pc idx) = checkIfBound env pc idx
termLocallyClosedRec _ (FreeVar _ _ _) = Right ()
termLocallyClosedRec env (XtorCall _ _ _ subst) = do
  sequence_ (pctermLocallyClosedRec env <$> subst)
termLocallyClosedRec env (XMatch _ _ _ cases) = do
  sequence_ ((\MkSCase { scase_cmd, scase_args } -> commandLocallyClosedRec (twiceMap (fmap (const ())) (fmap (const ())) scase_args : env) scase_cmd) <$> cases)
termLocallyClosedRec env (MuAbs _ PrdRep _ cmd) = commandLocallyClosedRec (Twice [] [()] : env) cmd
termLocallyClosedRec env (MuAbs _ CnsRep _ cmd) = commandLocallyClosedRec (Twice [()] [] : env) cmd
termLocallyClosedRec env (Dtor _ _ e args) = do
  termLocallyClosedRec env e
  sequence_ (termLocallyClosedRec env <$> args)
termLocallyClosedRec env (Match _ e cases) = do
  termLocallyClosedRec env e
  sequence_ (acaseLocallyClosedRec env <$> cases)
termLocallyClosedRec env (Comatch _ cases) =
  sequence_ (acaseLocallyClosedRec env <$> cases)

acaseLocallyClosedRec :: [Twice [()]] -> ACase ext -> Either Error ()
acaseLocallyClosedRec env (MkACase _ _ args e) = do
  termLocallyClosedRec ((Twice (const () <$> args) []):env) e

commandLocallyClosedRec :: [Twice [()]] -> Command ext -> Either Error ()
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

freeVarNamesToXtorArgs :: Twice [Maybe FreeVarName] -> Substitution Compiled
freeVarNamesToXtorArgs (Twice prds cnss) = prdArgs ++ cnsArgs
  where
    prdArgs = (\case {Just fv -> PrdTerm $ FreeVar () PrdRep fv; Nothing -> error "Create Names first!"}) <$> prds
    cnsArgs = (\case {Just fv -> CnsTerm $ FreeVar () CnsRep fv; Nothing -> error "Create Names first!"}) <$> cnss

openACase :: ACase ext -> ACase Compiled
openACase MkACase { acase_name, acase_args, acase_term } =
    MkACase { acase_ext = ()
            , acase_name = acase_name
            , acase_args = acase_args
            , acase_term = termOpening ((\case {Just fv ->  PrdTerm $ FreeVar () PrdRep fv; Nothing -> error "Create Names first!"}) <$> acase_args) (openSTermComplete acase_term)
            }

openSCase :: SCase ext -> SCase Compiled
openSCase MkSCase { scase_name, scase_args, scase_cmd } =
  MkSCase { scase_ext = ()
          , scase_name = scase_name
          , scase_args = scase_args
          , scase_cmd = commandOpening (freeVarNamesToXtorArgs scase_args) (openCommandComplete scase_cmd)
          }

openPCTermComplete :: PrdCnsTerm ext -> PrdCnsTerm Compiled
openPCTermComplete (PrdTerm tm) = PrdTerm $ openSTermComplete tm
openPCTermComplete (CnsTerm tm) = CnsTerm $ openSTermComplete tm

openSTermComplete :: Term pc ext -> Term pc Compiled
openSTermComplete (BoundVar _ pc idx) = BoundVar () pc idx
openSTermComplete (FreeVar _ pc v) = FreeVar () pc v
openSTermComplete (XtorCall _ pc name args) = XtorCall () pc name (openPCTermComplete <$> args)
openSTermComplete (XMatch _ pc ns cases) = XMatch () pc ns (openSCase <$> cases)
openSTermComplete (MuAbs _ PrdRep (Just fv) cmd) =
  MuAbs () PrdRep (Just fv) (commandOpeningSingle CnsRep (FreeVar () CnsRep fv) (openCommandComplete cmd))
openSTermComplete (MuAbs _ PrdRep Nothing _) = error "Create names first!"
openSTermComplete (MuAbs _ CnsRep (Just fv) cmd) =
  MuAbs () CnsRep (Just fv) (commandOpeningSingle PrdRep (FreeVar () PrdRep fv) (openCommandComplete cmd))
openSTermComplete (MuAbs _ CnsRep Nothing _) = error "Create names first!"
openSTermComplete (Dtor _ name t args) = Dtor () name (openSTermComplete t) (openSTermComplete <$> args)
openSTermComplete (Match _ t cases) = Match () (openSTermComplete t) (openACase <$> cases)
openSTermComplete (Comatch _ cocases) = Comatch () (openACase <$> cocases)

openCommandComplete :: Command ext -> Command Compiled
openCommandComplete (Apply _ t1 t2) = Apply () (openSTermComplete t1) (openSTermComplete t2)
openCommandComplete (Print _ t) = Print () (openSTermComplete t)
openCommandComplete (Done _) = Done ()

---------------------------------------------------------------------------------
-- CreateNames
---------------------------------------------------------------------------------

names :: ([FreeVarName], [FreeVarName])
names =  ((\y -> "x" <> T.pack (show y)) <$> [(1 :: Int)..]
         ,(\y -> "k" <> T.pack (show y)) <$> [(1 :: Int)..])

type CreateNameM a = State ([FreeVarName],[FreeVarName]) a

fresh :: PrdCnsRep pc -> CreateNameM (Maybe FreeVarName)
fresh PrdRep = do
  var <- gets (head . fst)
  modify (first tail)
  pure (Just var)
fresh CnsRep = do
  var  <- gets (head . snd)
  modify (second tail)
  pure (Just var)

createNamesSTerm :: Term pc ext -> Term pc Parsed
createNamesSTerm tm = evalState (createNamesSTerm' tm) names

createNamesCommand :: Command ext -> Command Parsed
createNamesCommand cmd = evalState (createNamesCommand' cmd) names

createNamesPCTerm :: PrdCnsTerm ext -> CreateNameM (PrdCnsTerm Parsed)
createNamesPCTerm (PrdTerm tm) = PrdTerm <$> createNamesSTerm' tm
createNamesPCTerm (CnsTerm tm) = CnsTerm <$> createNamesSTerm' tm

createNamesSTerm' :: Term pc ext -> CreateNameM (Term pc Parsed)
createNamesSTerm' (BoundVar _ pc idx) = return $ BoundVar defaultLoc pc idx
createNamesSTerm' (FreeVar _ pc nm)   = return $ FreeVar defaultLoc pc nm
createNamesSTerm' (XtorCall _ pc xt subst) = do
  subst' <- sequence $ createNamesPCTerm <$> subst
  return $ XtorCall defaultLoc pc xt subst'
createNamesSTerm' (XMatch _ pc ns cases) = do
  cases' <- sequence $ createNamesSCase <$> cases
  return $ XMatch defaultLoc pc ns cases'
createNamesSTerm' (MuAbs _ pc _ cmd) = do
  cmd' <- createNamesCommand' cmd
  var <- fresh (flipPrdCns pc)
  return $ MuAbs defaultLoc pc var cmd'
createNamesSTerm' (Dtor _ xt e args) = do
  e' <- createNamesSTerm' e
  args' <- sequence (createNamesSTerm' <$> args)
  return $ Dtor defaultLoc xt e' args'
createNamesSTerm' (Match _ e cases) = do
  e' <- createNamesSTerm' e
  cases' <- sequence (createNamesACase <$> cases)
  return $ Match defaultLoc e' cases'
createNamesSTerm' (Comatch _ cases) = do
  cases' <- sequence (createNamesACase <$> cases)
  return $ Comatch defaultLoc cases'

createNamesCommand' :: Command ext -> CreateNameM (Command Parsed)
createNamesCommand' (Done _) = return $ Done defaultLoc
createNamesCommand' (Apply _ prd cns) = do
  prd' <- createNamesSTerm' prd
  cns' <- createNamesSTerm' cns
  return (Apply defaultLoc prd' cns')
createNamesCommand' (Print _ prd) = createNamesSTerm' prd >>= \prd' -> return (Print defaultLoc prd')

createNamesSCase :: SCase ext -> CreateNameM (SCase Parsed)
createNamesSCase (MkSCase { scase_name, scase_args = Twice as bs, scase_cmd }) = do
  cmd' <- createNamesCommand' scase_cmd
  as' <- sequence $ (const (fresh PrdRep)) <$> as
  bs' <- sequence $ (const (fresh CnsRep)) <$> bs
  return $ MkSCase defaultLoc scase_name (Twice as' bs') cmd'

createNamesACase :: ACase ext -> CreateNameM (ACase Parsed)
createNamesACase (MkACase _ xt args e) = do
  e' <- createNamesSTerm' e
  args' <- sequence $ (const (fresh PrdRep)) <$> args
  return $ MkACase defaultLoc xt args' e'



---------------------------------------------------------------------------------
-- Shifting
--
-- Used in program transformations like focusing.
---------------------------------------------------------------------------------

shiftPCTerm :: Int -> PrdCnsTerm ext -> PrdCnsTerm ext
shiftPCTerm n (PrdTerm tm) = PrdTerm $ shiftSTerm' n tm
shiftPCTerm n (CnsTerm tm) = CnsTerm $ shiftSTerm' n tm

shiftSTerm' :: Int -> Term pc ext -> Term pc ext
shiftSTerm' _ var@FreeVar {} = var
shiftSTerm' n (BoundVar ext pcrep (i,j)) | n <= i    = BoundVar ext pcrep (i + 1, j)
                                         | otherwise = BoundVar ext pcrep (i    , j)
shiftSTerm' n (XtorCall ext pcrep name subst) =
    XtorCall ext pcrep name (shiftPCTerm n <$> subst)
shiftSTerm' n (XMatch ext pcrep ns cases) = XMatch ext pcrep ns (shiftSCase (n + 1) <$> cases)
shiftSTerm' n (MuAbs ext pcrep bs cmd) = MuAbs ext pcrep bs (shiftCmd' (n + 1) cmd)
shiftSTerm' n (Dtor ext xt e args) = Dtor ext xt (shiftSTerm' n e) (shiftSTerm' n <$> args)
shiftSTerm' n (Match ext e cases) = Match ext (shiftSTerm' n e) (shiftACase n <$> cases)
shiftSTerm' n (Comatch ext cases) = Comatch ext (shiftACase n <$> cases)

shiftACase :: Int -> ACase ext -> ACase ext
shiftACase n (MkACase ext xt args e) = MkACase ext xt args (shiftSTerm' n e)

shiftSCase :: Int -> SCase ext-> SCase ext
shiftSCase n (MkSCase ext name bs cmd) = MkSCase ext name bs (shiftCmd' n cmd)

shiftCmd' :: Int -> Command ext -> Command ext
shiftCmd' n (Apply ext prd cns) = Apply ext (shiftSTerm' n prd) (shiftSTerm' n cns)
shiftCmd' _ (Done ext) = Done ext
shiftCmd' n (Print ext prd) = Print ext (shiftSTerm' n prd)

-- | Shift all unbound BoundVars up by one.
shiftSTerm :: Term pc ext -> Term pc ext
shiftSTerm = shiftSTerm' 0

-- | Shift all unbound BoundVars up by one.
shiftCmd :: Command ext -> Command ext
shiftCmd = shiftCmd' 0

---------------------------------------------------------------------------------
-- Remove Names
--
-- Replaces all variable binding sites with Nothing
---------------------------------------------------------------------------------

removeNamesPrdCnsTerm :: PrdCnsTerm ext -> PrdCnsTerm ext
removeNamesPrdCnsTerm (PrdTerm tm) = PrdTerm $ removeNamesSTerm tm
removeNamesPrdCnsTerm (CnsTerm tm) = CnsTerm $ removeNamesSTerm tm

removeNamesSTerm :: Term pc  ext -> Term pc ext
removeNamesSTerm f@FreeVar{} = f
removeNamesSTerm f@BoundVar{} = f
removeNamesSTerm (XtorCall ext pc xt args) = XtorCall ext pc xt (removeNamesPrdCnsTerm <$> args)
removeNamesSTerm (MuAbs ext pc _ cmd) = MuAbs ext pc Nothing (removeNamesCmd cmd)
removeNamesSTerm (XMatch ext pc ns cases) = XMatch ext pc ns (removeNamesSCase <$> cases)
removeNamesSTerm (Dtor ext xt e args) = Dtor ext xt (removeNamesSTerm e) (removeNamesSTerm <$> args)
removeNamesSTerm (Match ext e cases) = Match ext (removeNamesSTerm e) (removeNamesACase <$> cases)
removeNamesSTerm (Comatch ext cases) = Comatch ext (removeNamesACase <$> cases)

removeNamesACase :: ACase ext -> ACase ext
removeNamesACase (MkACase ext xt args e) = MkACase ext xt (const Nothing <$> args) (removeNamesSTerm e)

removeNamesSCase :: SCase ext -> SCase ext
removeNamesSCase (MkSCase ext xt args cmd)= MkSCase ext xt (fmap (const Nothing) <$> args) (removeNamesCmd cmd)

removeNamesCmd :: Command ext -> Command ext
removeNamesCmd (Apply ext prd cns) = Apply ext (removeNamesSTerm prd) (removeNamesSTerm cns)
removeNamesCmd (Print ext prd) = Print ext (removeNamesSTerm prd)
removeNamesCmd (Done ext) = Done ext