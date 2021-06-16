module TypeInference.GenerateConstraints.Definition
  ( -- Constraint Generation Monad
    GenM
  , GenerateReader(..)
  , runGenM
    -- Generating fresh unification variables
  , freshTVar
  , freshTVars
    -- Throwing errors
  , throwGenError
    -- Looking up in context or environment
  , lookupContext
  , lookupPrdEnv
  , lookupCnsEnv
  , lookupDefEnv
    -- Running computations in extended context or environment.
  , withContext
  , withPrdEnv
  , withCnsEnv
  , withDefEnv
    -- Instantiating type schemes
  , instantiateTypeScheme
    -- Adding a constraint
  , addConstraint
    -- Other
  , InferenceMode(..)
  , PrdCnsToPol
  , lookupDataDecl
  , lookupXtorSig
  , xtorSigMakeStructural
  , lookupCase
  , foo
  , prdCnsToPol
  , checkExhaustiveness
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text as T

import Pretty.Pretty
import Pretty.STerms ()
import Pretty.ATerms ()
import Pretty.Types ()
import Syntax.ATerms
import Syntax.Program
import Syntax.STerms
import Syntax.Types
import Utils
import Data.List

---------------------------------------------------------------------------------------------
-- GenerateState:
--
-- We use varCount for generating fresh type variables.
-- We collect all generated unification variables and constraints in a ConstraintSet.
---------------------------------------------------------------------------------------------

data GenerateState = GenerateState
  { varCount :: Int
  , constraintSet :: ConstraintSet
  }

initialConstraintSet :: ConstraintSet
initialConstraintSet = ConstraintSet { cs_constraints = [], cs_uvars = [] }

initialState :: GenerateState
initialState = GenerateState { varCount = 0, constraintSet = initialConstraintSet }

---------------------------------------------------------------------------------------------
-- GenerateReader:
--
-- We have access to a program environment and a local variable context.
-- The context contains monotypes, whereas the environment contains type schemes.
---------------------------------------------------------------------------------------------

data GenerateReader = GenerateReader { context :: [TypArgs Pos]
                                     , env :: Environment FreeVarName
                                     , inferMode :: InferenceMode
                                     }

initialReader :: Environment FreeVarName -> InferenceMode -> GenerateReader
initialReader env im = GenerateReader { context = [], env = env, inferMode = im }

---------------------------------------------------------------------------------------------
-- GenM
---------------------------------------------------------------------------------------------

newtype GenM a = GenM { getGenM :: ReaderT GenerateReader (StateT GenerateState (Except Error)) a }
  deriving (Functor, Applicative, Monad, MonadState GenerateState, MonadReader GenerateReader, MonadError Error)

runGenM :: Environment FreeVarName -> InferenceMode -> GenM a -> Either Error (a, ConstraintSet)
runGenM env im m = case runExcept (runStateT (runReaderT  (getGenM m) (initialReader env im)) initialState) of
  Left err -> Left err
  Right (x, state) -> Right (x, constraintSet state)

---------------------------------------------------------------------------------------------
-- Throwing errors
---------------------------------------------------------------------------------------------

throwGenError :: Text -> GenM a
throwGenError msg = throwError $ GenConstraintsError msg

---------------------------------------------------------------------------------------------
-- Generating fresh unification variables
---------------------------------------------------------------------------------------------

freshTVar :: UVarProvenance -> GenM (Typ Pos, Typ Neg)
freshTVar uvp = do
  var <- gets varCount
  let tvar = MkTVar ("u" <> T.pack (show var))
  -- We need to increment the counter:
  modify (\gs@GenerateState{} -> gs { varCount = var + 1 })
  -- We also need to add the uvar to the constraintset.
  modify (\gs@GenerateState{ constraintSet = cs@ConstraintSet { cs_uvars } } ->
            gs { constraintSet = cs { cs_uvars = cs_uvars ++ [(tvar, uvp)] } })
  return (TyVar PosRep tvar, TyVar NegRep tvar)

freshTVars :: Twice [FreeVarName] -> GenM (TypArgs Pos, TypArgs Neg)
freshTVars (Twice prdArgs cnsArgs) = do
  (prdArgsPos, prdArgsNeg) <- unzip <$> forM prdArgs (\fv -> freshTVar (ProgramVariable fv))
  (cnsArgsPos, cnsArgsNeg) <- unzip <$> forM cnsArgs (\fv -> freshTVar (ProgramVariable fv))
  return (MkTypArgs prdArgsPos cnsArgsNeg, MkTypArgs prdArgsNeg cnsArgsPos)

---------------------------------------------------------------------------------------------
-- Running computations in an extended context or environment
---------------------------------------------------------------------------------------------

withContext :: TypArgs 'Pos -> GenM a -> GenM a
withContext ctx m =
  local (\gr@GenerateReader{..} -> gr { context = ctx:context }) m

withPrdEnv :: FreeVarName -> STerm Prd () FreeVarName -> TypeScheme Pos -> GenM a -> GenM a
withPrdEnv fv tm tys m = do
  let modifyEnv (GenerateReader ctx env@Environment { prdEnv } im) =
        GenerateReader ctx env { prdEnv = M.insert fv (tm,tys) prdEnv } im
  local modifyEnv m

withCnsEnv :: FreeVarName -> STerm Cns () FreeVarName -> TypeScheme Neg -> GenM a -> GenM a
withCnsEnv fv tm tys m = do
  let modifyEnv (GenerateReader ctx env@Environment { cnsEnv } im) =
        GenerateReader ctx env { cnsEnv = M.insert fv (tm,tys) cnsEnv } im
  local modifyEnv m

withDefEnv :: FreeVarName -> ATerm () FreeVarName -> TypeScheme Pos -> GenM a -> GenM a
withDefEnv fv tm tys m = do
  let modifyEnv (GenerateReader ctx env@Environment { defEnv } im) =
        GenerateReader ctx env { defEnv = M.insert fv (tm,tys) defEnv } im
  local modifyEnv m

---------------------------------------------------------------------------------------------
-- Looking up types in the context and environment
---------------------------------------------------------------------------------------------

-- | Lookup a type of a bound variable in the context.
lookupContext :: PrdCnsRep pc -> Index -> GenM (Typ (PrdCnsToPol pc))
lookupContext rep (i,j) = do
  ctx <- asks context
  case indexMaybe ctx i of
    Nothing -> throwGenError $ "Bound Variable out of bounds: " <> T.pack (show (i,j))
    Just (MkTypArgs { prdTypes, cnsTypes }) -> case rep of
      PrdRep -> do
        case indexMaybe prdTypes j of
          Nothing -> throwGenError $ "Bound Variable out of bounds: " <> T.pack (show (i,j))
          Just ty -> return ty
      CnsRep -> do
        case indexMaybe cnsTypes j of
          Nothing -> throwGenError $ "Bound Variable out of bounds: " <> T.pack (show (i,j))
          Just ty -> return ty

lookupPrdEnv :: FreeVarName -> GenM (TypeScheme Pos)
lookupPrdEnv fv = do
  prdEnv <- asks (prdEnv . env)
  case M.lookup fv prdEnv of
    Just (_,tys) -> return tys
    Nothing ->
      throwGenError $ "Unbound free producer variable:" <> ppPrint fv

lookupCnsEnv :: FreeVarName -> GenM (TypeScheme Neg)
lookupCnsEnv fv = do
  cnsEnv <- asks (cnsEnv . env)
  case M.lookup fv cnsEnv of
    Just (_,tys) -> return tys
    Nothing ->
      throwGenError $ "Unbound free consumer variable:" <> ppPrint fv

lookupDefEnv :: FreeVarName -> GenM (TypeScheme Pos)
lookupDefEnv fv = do
  defEnv <- asks (defEnv . env)
  case M.lookup fv defEnv of
    Just (_,tys) -> return tys
    Nothing ->
      throwGenError $ "Unbound free def variable:" <> ppPrint fv

---------------------------------------------------------------------------------------------
-- Instantiating type schemes with fresh unification variables.
---------------------------------------------------------------------------------------------

instantiateTypeScheme :: FreeVarName -> Loc -> TypeScheme pol -> GenM (Typ pol)
instantiateTypeScheme fv loc TypeScheme { ts_vars, ts_monotype } = do
  freshVars <- forM ts_vars (\tv -> freshTVar (TypeSchemeInstance fv loc) >>= \ty -> return (tv, ty))
  return $ substituteType (M.fromList freshVars) ts_monotype

---------------------------------------------------------------------------------------------
-- Adding a constraint
---------------------------------------------------------------------------------------------

-- | Add a constraint to the state.
addConstraint :: Constraint ConstraintInfo -> GenM ()
addConstraint c = modify foo
  where
    foo gs@GenerateState { constraintSet } = gs { constraintSet = bar constraintSet }
    bar cs@ConstraintSet { cs_constraints } = cs { cs_constraints = c:cs_constraints }

---------------------------------------------------------------------------------------------
-- Other
---------------------------------------------------------------------------------------------

-- | Specifies whether to infer nominal or refined types
data InferenceMode = InferNominal | InferRefined
  deriving (Eq, Show)

-- | We map producer terms to positive types, and consumer terms to negative types.
type family PrdCnsToPol (pc :: PrdCns) :: Polarity where
  PrdCnsToPol Prd = Pos
  PrdCnsToPol Cns = Neg

prdCnsToPol :: PrdCnsRep pc -> PolarityRep (PrdCnsToPol pc)
prdCnsToPol PrdRep = PosRep
prdCnsToPol CnsRep = NegRep

foo :: PrdCnsRep pc -> PolarityRep (PrdCnsToPol pc)
foo PrdRep = PosRep
foo CnsRep = NegRep

lookupCase :: XtorName -> GenM (TypArgs Pos, XtorArgs () FreeVarName)
lookupCase xt = do
  env <- asks env
  case M.lookup xt (envToXtorMap env) of
    Nothing -> throwGenError $ "GenerateConstraints: The xtor " <> ppPrint xt <> " could not be looked up."
    Just types@(MkTypArgs prdTypes cnsTypes) -> do
      let prds = (\_ -> FreeVar () PrdRep "y") <$> prdTypes
      let cnss = (\_ -> FreeVar () CnsRep "y") <$> cnsTypes
      return (types, MkXtorArgs prds cnss)

lookupDataDecl :: XtorName -> GenM DataDecl
lookupDataDecl xt = do
  env <- asks env
  case lookupXtor xt env of
    Nothing -> throwGenError $ "Constructor/Destructor " <> ppPrint xt <> " is not contained in program."
    Just decl -> return decl

lookupXtorSig :: DataDecl -> XtorName -> PolarityRep pol -> GenM (XtorSig pol)
lookupXtorSig decl xtn pol = do
  case find ( \MkXtorSig{..} -> sig_name == xtn ) (data_xtors decl pol) of
    Just xts -> return xts
    Nothing -> throwGenError $ "XtorName " <> unXtorName xtn <> " not found in declaration of type " <> unTypeName (data_name decl)

xtorSigMakeStructural :: XtorSig pol -> XtorSig pol
xtorSigMakeStructural (MkXtorSig (MkXtorName _ s) MkTypArgs{..}) =
  MkXtorSig (MkXtorName Structural s) (MkTypArgs prdTypes cnsTypes)

-- | Checks for a given list of XtorNames and a type declaration whether:
-- (1) All the xtornames occur in the type declaration. (Correctness)
-- (2) All xtors of the type declaration are matched against. (Exhaustiveness)
checkExhaustiveness :: [XtorName] -- ^ The xtor names used in the pattern match
                    -> DataDecl   -- ^ The type declaration to check against.
                    -> GenM ()
checkExhaustiveness matched decl = do
  let declared = sig_name <$> data_xtors decl PosRep
  forM_ matched $ \xn -> unless (xn `elem` declared) 
    (throwGenError ("Pattern Match Error. The xtor " <> ppPrint xn <> " does not occur in the declaration of type " <> ppPrint (data_name decl)))
  im <- asks inferMode
  -- Only check exhaustiveness when not using refinements
  case im of
    InferRefined -> return ()
    InferNominal ->
      forM_ declared $ \xn -> unless (xn `elem` matched)
        (throwGenError ("Pattern Match Exhaustiveness Error. Xtor: " <> ppPrint xn <> " of type " <>
          ppPrint (data_name decl) <> " is not matched against." ))

