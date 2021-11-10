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
import Syntax.Types 
import Syntax.CommonTerm (Phase(Compiled))
import Control.Monad.Except (ExceptT)

---------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------

type family ACaseExt (ext :: Phase) :: Type where
  ACaseExt Parsed = Loc
  ACaseExt Inferred = Loc
  ACaseExt Compiled = ()

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
  { acase_ext :: ACaseExt ext
  , acase_name :: XtorName
  , acase_args :: [Maybe FreeVarName]
  , acase_term :: STerm Prd ext
  }

deriving instance (Eq (ACase Parsed))
deriving instance (Eq (ACase Inferred))
deriving instance (Eq (ACase Compiled))
deriving instance (Show (ACase Parsed))
deriving instance (Show (ACase Inferred))
deriving instance (Show (ACase Compiled))

---------------------------------------------------------------------------------
-- # Terms
-- 
-- ## Variable representation
--
-- We use the locally nameless representation for terms, which combines names for
-- free variables with  anonymous deBruijn indexes for bound variables.
-- The locally namelesss representation is well documented here:
-- https://www.chargueraud.org/softs/ln/
---------------------------------------------------------------------------------

-- | Represents an argument list to a constructor or destructor.
data XtorArgs ext = MkXtorArgs { prdArgs :: [STerm Prd ext]
                               , cnsArgs :: [STerm Cns ext]
                               }

deriving instance (Eq (XtorArgs Parsed))
deriving instance (Eq (XtorArgs Inferred))
deriving instance (Eq (XtorArgs Compiled))
deriving instance (Show (XtorArgs Parsed))
deriving instance (Show (XtorArgs Inferred))
deriving instance (Show (XtorArgs Compiled))

-- | Represents one case in a pattern match or copattern match.
--
--        X(x_1,...,x_n)[k_1,...,k_m] => c
--        ^ ^^^^^^^^^^^^^^^^^^^^^^^^     ^
--        |              |               |
--    scase_name     scase_args      scase_cmd
--
data SCase (ext :: Phase) = MkSCase
  { scase_name :: XtorName
  , scase_args :: Twice [Maybe FreeVarName]
  , scase_cmd  :: Command ext
  }

deriving instance (Eq (SCase Parsed))
deriving instance (Eq (SCase Inferred))
deriving instance (Eq (SCase Compiled))
deriving instance (Show (SCase Parsed))
deriving instance (Show (SCase Inferred))
deriving instance (Show (SCase Compiled))

type family STermExt (pc :: PrdCns) (ext :: Phase) :: Type where
  STermExt _ Parsed = Loc
  STermExt Prd Inferred = (Loc, Typ Pos)
  STermExt Cns Inferred = (Loc, Typ Neg)
  STermExt _ Compiled = ()

-- | A symmetric term.
-- The `bs` parameter is used to store additional information at binding sites.
data STerm (pc :: PrdCns) (ext :: Phase) where
  -- | A bound variable in the locally nameless system.
  BoundVar :: STermExt pc ext -> PrdCnsRep pc -> Index -> STerm pc ext
  -- | A free variable in the locally nameless system.
  FreeVar :: STermExt pc ext -> PrdCnsRep pc -> FreeVarName -> STerm pc ext
  -- | A constructor or destructor.
  -- If the first argument is `PrdRep` it is a constructor, a destructor otherwise.
  XtorCall :: STermExt pc ext -> PrdCnsRep pc -> XtorName -> XtorArgs ext -> STerm pc ext
  -- | A pattern or copattern match.
  -- If the first argument is `PrdRep` it is a copattern match, a pattern match otherwise.
  XMatch :: STermExt pc ext -> PrdCnsRep pc -> NominalStructural -> [SCase ext] -> STerm pc ext
  -- | A Mu or TildeMu abstraction:
  --
  --  mu k.c    =   MuAbs PrdRep c
  -- ~mu x.c    =   MuAbs CnsRep c
  MuAbs :: STermExt pc ext -> PrdCnsRep pc -> Maybe FreeVarName -> Command ext -> STerm pc ext
  --
  -- Asymmetric Terms!
  --
  Dtor :: STermExt Prd ext -> XtorName -> STerm Prd ext -> [STerm Prd ext] -> STerm Prd ext
  -- | A pattern match:
  --
  -- match e with { ... }
  --
  Match :: STermExt Prd ext -> STerm Prd ext -> [ACase ext] -> STerm Prd ext
  -- | A copattern match:
  --
  -- comatch { ... }
  --
  Comatch :: STermExt Prd ext -> [ACase ext] -> STerm Prd ext



deriving instance (Eq (STerm pc Parsed))
deriving instance (Eq (STerm Prd Inferred))
deriving instance (Eq (STerm Cns Inferred))
deriving instance (Eq (STerm pc Compiled))
deriving instance (Show (STerm pc Parsed))
deriving instance (Show (STerm Prd Inferred))
deriving instance (Show (STerm Cns Inferred))
deriving instance (Show (STerm pc Compiled))

getTypeSTerm :: STerm pc Inferred -> Typ (PrdCnsToPol pc)
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

getTypArgs :: XtorArgs Inferred -> TypArgs Pos
getTypArgs (MkXtorArgs prdArgs cnsArgs )= MkTypArgs (getTypeSTerm <$> prdArgs) (getTypeSTerm <$> cnsArgs)

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
  Apply :: CommandExt ext -> STerm Prd ext -> STerm Cns ext -> Command ext
  Print :: CommandExt ext -> STerm Prd ext -> Command ext
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

--atermOpeningRec :: Int -> [ATerm Compiled] -> ATerm Compiled -> ATerm Compiled
termOpeningRec :: Int -> XtorArgs Compiled -> STerm pc Compiled -> STerm pc Compiled
termOpeningRec k MkXtorArgs { prdArgs } bv@(BoundVar _ PrdRep (i,j)) | i == k    = prdArgs !! j
                                                                     | otherwise = bv
termOpeningRec k MkXtorArgs { cnsArgs } bv@(BoundVar _ CnsRep (i,j)) | i == k    = cnsArgs !! j
                                                                     | otherwise = bv
termOpeningRec _ _ fv@(FreeVar _ _ _)       = fv
termOpeningRec k args (XtorCall _ s xt (MkXtorArgs prdArgs cnsArgs)) =
  XtorCall () s xt (MkXtorArgs (termOpeningRec k args <$> prdArgs)
                               (termOpeningRec k args <$> cnsArgs))
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

termOpening :: XtorArgs Compiled -> STerm pc Compiled -> STerm pc Compiled
termOpening = termOpeningRec 0

commandOpeningRec :: Int -> XtorArgs Compiled -> Command Compiled -> Command Compiled
commandOpeningRec _ _ (Done _) = Done ()
commandOpeningRec k args (Print _ t) = Print () (termOpeningRec k args t)
commandOpeningRec k args (Apply _ t1 t2) = Apply () (termOpeningRec k args t1) (termOpeningRec k args t2)


-- replaces bound variables pointing "outside" of a command with given arguments
commandOpening :: XtorArgs Compiled -> Command Compiled -> Command Compiled
commandOpening = commandOpeningRec 0

commandOpeningSingle :: PrdCnsRep pc -> STerm pc Compiled -> Command Compiled -> Command Compiled
commandOpeningSingle PrdRep t = commandOpening (MkXtorArgs [t] [])
commandOpeningSingle CnsRep t = commandOpening (MkXtorArgs [] [t])

---------------------------------------------------------------------------------
-- Variable Closing
---------------------------------------------------------------------------------



--atermClosingRec :: Int -> [FreeVarName] -> ATerm ext -> ATerm ext
termClosingRec :: Int -> Twice [FreeVarName] -> STerm pc ext -> STerm pc ext
termClosingRec _ _ bv@(BoundVar _ _ _) = bv
termClosingRec k (Twice prdvars _) (FreeVar ext PrdRep v) | isJust (v `elemIndex` prdvars) = BoundVar ext PrdRep (k, fromJust (v `elemIndex` prdvars))
                                                          | otherwise = FreeVar ext PrdRep v
termClosingRec k (Twice _ cnsvars) (FreeVar ext CnsRep v) | isJust (v `elemIndex` cnsvars) = BoundVar ext CnsRep (k, fromJust (v `elemIndex` cnsvars))
                                                          | otherwise = FreeVar ext CnsRep v
termClosingRec k vars (XtorCall ext s xt (MkXtorArgs prdArgs cnsArgs)) =
  XtorCall ext s xt (MkXtorArgs (termClosingRec k vars <$> prdArgs)(termClosingRec k vars <$> cnsArgs))
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

termLocallyClosedRec :: [Twice [()]] -> STerm pc ext -> Either Error ()
termLocallyClosedRec env (BoundVar _ pc idx) = checkIfBound env pc idx
termLocallyClosedRec _ (FreeVar _ _ _) = Right ()
termLocallyClosedRec env (XtorCall _ _ _ (MkXtorArgs prds cnss)) = do
  sequence_ (termLocallyClosedRec env <$> prds)
  sequence_ (termLocallyClosedRec env <$> cnss)
termLocallyClosedRec env (XMatch _ _ _ cases) = do
  sequence_ ((\MkSCase { scase_cmd, scase_args } -> commandLocallyClosedRec (twiceMap (fmap (const ())) (fmap (const ())) scase_args : env) scase_cmd) <$> cases)
termLocallyClosedRec env (MuAbs _ PrdRep _ cmd) = commandLocallyClosedRec (Twice [] [()] : env) cmd
termLocallyClosedRec env (MuAbs _ CnsRep _ cmd) = commandLocallyClosedRec (Twice [()] [] : env) cmd

commandLocallyClosedRec :: [Twice [()]] -> Command ext -> Either Error ()
commandLocallyClosedRec _ (Done _) = Right ()
commandLocallyClosedRec env (Print _ t) = termLocallyClosedRec env t
commandLocallyClosedRec env (Apply _ t1 t2) = termLocallyClosedRec env t1 >> termLocallyClosedRec env t2

termLocallyClosed :: STerm pc ext -> Either Error ()
termLocallyClosed = termLocallyClosedRec []

commandLocallyClosed :: Command ext -> Either Error ()
commandLocallyClosed = commandLocallyClosedRec []

---------------------------------------------------------------------------------
-- These functions  translate a locally nameless term into a named representation.
--
-- Use only for prettyprinting! These functions only "undo" the steps in the parser
-- and do not fulfil any semantic properties w.r.t shadowing etc.!
---------------------------------------------------------------------------------

openXtorArgsComplete :: XtorArgs ext -> XtorArgs Compiled
openXtorArgsComplete (MkXtorArgs prdArgs cnsArgs) =
  MkXtorArgs (openSTermComplete <$> prdArgs) (openSTermComplete <$> cnsArgs)

freeVarNamesToXtorArgs :: Twice [Maybe FreeVarName] -> XtorArgs Compiled
freeVarNamesToXtorArgs (Twice prds cnss) = MkXtorArgs ((\case {Just fv -> FreeVar () PrdRep fv; Nothing -> error "Create Names first!"}) <$> prds)
                                                      ((\case {Just fv -> FreeVar () CnsRep fv; Nothing -> error "Create Names first!"}) <$> cnss)

openSTermComplete :: STerm pc ext -> STerm pc Compiled
openSTermComplete (BoundVar _ pc idx) = BoundVar () pc idx
openSTermComplete (FreeVar _ pc v) = FreeVar () pc v
openSTermComplete (XtorCall _ pc name args) = XtorCall () pc name (openXtorArgsComplete args)
openSTermComplete (XMatch _ pc ns cases) = let
  openSCase :: SCase ext -> SCase Compiled
  openSCase MkSCase { scase_name, scase_args, scase_cmd } =
    MkSCase { scase_name = scase_name
            , scase_args = scase_args
            , scase_cmd = commandOpening (freeVarNamesToXtorArgs scase_args) (openCommandComplete scase_cmd)
            }
  in XMatch () pc ns (openSCase <$> cases)
openSTermComplete (MuAbs _ PrdRep (Just fv) cmd) =
  MuAbs () PrdRep (Just fv) (commandOpeningSingle CnsRep (FreeVar () CnsRep fv) (openCommandComplete cmd))
openSTermComplete (MuAbs _ PrdRep Nothing _) = error "Create names first!"
openSTermComplete (MuAbs _ CnsRep (Just fv) cmd) =
  MuAbs () CnsRep (Just fv) (commandOpeningSingle PrdRep (FreeVar () PrdRep fv) (openCommandComplete cmd))
openSTermComplete (MuAbs _ CnsRep Nothing _) = error "Create names first!"
openSTermComplete (Dtor _ name t args) = Dtor () name (openSTermComplete t) (openSTermComplete <$> args)
openSTermComplete (Match _ t cases) = Match () (openSTermComplete t) (openACase <$> cases)
openSTermComplete (Comatch _ cocases) = Comatch () (openACase <$> cocases)

---------------------------------------------------------------------------------
-- These functions  translate a locally nameless term into a named representation.
--
-- Use only for prettyprinting! These functions only "undo" the steps in the parser
-- and do not fulfil any semantic properties w.r.t shadowing etc.!
---------------------------------------------------------------------------------

openACase :: ACase ext -> ACase Compiled
openACase MkACase { acase_name, acase_args, acase_term } =
    MkACase { acase_ext = ()
            , acase_name = acase_name
            , acase_args = acase_args
            , acase_term = termOpening (MkXtorArgs ((\case {Just fv ->  FreeVar () PrdRep fv; Nothing -> error "Create Names first!"}) <$> acase_args) []) (openSTermComplete acase_term)
            }



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

createNamesSTerm :: STerm pc ext -> STerm pc ext
createNamesSTerm tm = evalState (createNamesSTerm' tm) names

createNamesCommand :: Command ext -> Command ext
createNamesCommand cmd = evalState (createNamesCommand' cmd) names

createNamesSTerm' :: STerm pc ext -> CreateNameM (STerm pc ext)
createNamesSTerm' (BoundVar ext pc idx) = return $ BoundVar ext pc idx
createNamesSTerm' (FreeVar ext pc nm)   = return $ FreeVar ext pc nm
createNamesSTerm' (XtorCall ext pc xt MkXtorArgs { prdArgs, cnsArgs}) = do
  prdArgs' <- sequence $ createNamesSTerm' <$> prdArgs
  cnsArgs' <- sequence $ createNamesSTerm' <$> cnsArgs
  return $ XtorCall ext pc xt (MkXtorArgs prdArgs' cnsArgs')
createNamesSTerm' (XMatch ext pc ns cases) = do
  cases' <- sequence $ createNamesCase <$> cases
  return $ XMatch ext pc ns cases'
createNamesSTerm' (MuAbs ext pc _ cmd) = do
  cmd' <- createNamesCommand' cmd
  var <- fresh (flipPrdCns pc)
  return $ MuAbs ext pc var cmd'

createNamesCommand' :: Command ext -> CreateNameM (Command ext)
createNamesCommand' (Done ext) = return $ Done ext
createNamesCommand' (Apply ext prd cns) = do
  prd' <- createNamesSTerm' prd 
  cns' <- createNamesSTerm' cns 
  return (Apply ext prd' cns')
createNamesCommand' (Print ext prd) = createNamesSTerm' prd >>= \prd' -> return (Print ext prd')

createNamesCase :: SCase ext -> CreateNameM (SCase ext)
createNamesCase (MkSCase {scase_name, scase_args = Twice as bs, scase_cmd }) = do
  cmd' <- createNamesCommand' scase_cmd
  as' <- sequence $ (const (fresh PrdRep)) <$> as
  bs' <- sequence $ (const (fresh CnsRep)) <$> bs
  return $ MkSCase scase_name (Twice as' bs') cmd'


---------------------------------------------------------------------------------
-- Shifting
--
-- Used in program transformations like focusing.
---------------------------------------------------------------------------------

shiftSTerm' :: Int -> STerm pc ext -> STerm pc ext
shiftSTerm' _ var@FreeVar {} = var
shiftSTerm' n (BoundVar ext pcrep (i,j)) | n <= i    = BoundVar ext pcrep (i + 1, j)
                                         | otherwise = BoundVar ext pcrep (i    , j)
shiftSTerm' n (XtorCall ext pcrep name MkXtorArgs { prdArgs, cnsArgs }) =
    XtorCall ext pcrep name (MkXtorArgs (shiftSTerm' n <$> prdArgs) (shiftSTerm' n <$> cnsArgs))
shiftSTerm' n (XMatch ext pcrep ns cases) = XMatch ext pcrep ns (shiftSCase (n + 1) <$> cases)
shiftSTerm' n (MuAbs ext pcrep bs cmd) = MuAbs ext pcrep bs (shiftCmd' (n + 1) cmd)
shiftSTerm' n (Dtor ext xt e args) = Dtor ext xt (shiftSTerm' n e) (shiftSTerm' n <$> args)
shiftSTerm' n (Match ext e cases) = Match ext (shiftSTerm' n e) (shiftACase n <$> cases)
shiftSTerm' n (Comatch ext cases) = Comatch ext (shiftACase n <$> cases)

shiftACase :: Int -> ACase ext -> ACase ext
shiftACase n (MkACase ext xt args e) = MkACase ext xt args (shiftSTerm' n e)

shiftSCase :: Int -> SCase ext-> SCase ext
shiftSCase n (MkSCase name bs cmd) = MkSCase name bs (shiftCmd' n cmd)

shiftCmd' :: Int -> Command ext -> Command ext
shiftCmd' n (Apply ext prd cns) = Apply ext (shiftSTerm' n prd) (shiftSTerm' n cns)
shiftCmd' _ (Done ext) = Done ext
shiftCmd' n (Print ext prd) = Print ext (shiftSTerm' n prd)

-- | Shift all unbound BoundVars up by one.
shiftSTerm :: STerm pc ext -> STerm pc ext
shiftSTerm = shiftSTerm' 0

-- | Shift all unbound BoundVars up by one.
shiftCmd :: Command ext -> Command ext
shiftCmd = shiftCmd' 0

---------------------------------------------------------------------------------
-- Remove Names
--
-- Replaces all variable binding sites with Nothing
---------------------------------------------------------------------------------

removeNamesSTerm :: STerm pc  ext -> STerm pc ext 
removeNamesSTerm f@FreeVar{} = f
removeNamesSTerm f@BoundVar{} = f
removeNamesSTerm (XtorCall ext pc xt (MkXtorArgs prdArgs cnsArgs)) = XtorCall ext pc xt (MkXtorArgs (removeNamesSTerm <$> prdArgs) (removeNamesSTerm <$> cnsArgs))
removeNamesSTerm (MuAbs ext pc _ cmd) = MuAbs ext pc Nothing (removeNamesCmd cmd)
removeNamesSTerm (XMatch ext pc ns cases) = XMatch ext pc ns (removeNamesSCase <$> cases)
removeNamesSTerm (Dtor ext xt e args) = Dtor ext xt (removeNamesSTerm e) (removeNamesSTerm <$> args)
removeNamesSTerm (Match ext e cases) = Match ext (removeNamesSTerm e) (removeNamesACase <$> cases)
removeNamesSTerm (Comatch ext cases) = Comatch ext (removeNamesACase <$> cases)

removeNamesACase :: ACase ext -> ACase ext
removeNamesACase (MkACase ext xt args e) = MkACase ext xt (const Nothing <$> args) (removeNamesSTerm e)

removeNamesSCase :: SCase ext -> SCase ext
removeNamesSCase (MkSCase xt args cmd)= MkSCase xt (fmap (const Nothing) <$> args) (removeNamesCmd cmd)

removeNamesCmd :: Command ext -> Command ext 
removeNamesCmd (Apply ext prd cns) = Apply ext (removeNamesSTerm prd) (removeNamesSTerm cns)
removeNamesCmd (Print ext prd) = Print ext (removeNamesSTerm prd)
removeNamesCmd (Done ext) = Done ext