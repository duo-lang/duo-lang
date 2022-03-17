module TypeInference.GenerateConstraints.Definition
  ( -- Constraint Generation Monad
    GenM
  , GenerateReader(..)
  , runGenM
    -- Generating fresh unification variables
  , freshTVar
  , freshTVars
  , freshTVarsForTypeParams
    -- Throwing errors
  , throwGenError
    -- Looking up in context or environment
  , lookupContext
    -- Running computations in extended context or environment.
  , withContext
    -- Instantiating type schemes
  , instantiateTypeScheme
    -- Adding a constraint
  , addConstraint
    -- Other
  , PrdCnsToPol
  , foo
  , fromMaybeVar
  , prdCnsToPol
  , checkCorrectness
  , checkExhaustiveness
  , translateXtorSigUpper
  , translateTypeUpper
  , translateXtorSigLower
  , translateTypeLower
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import Data.Map qualified as M
import Data.Text qualified as T

import Errors
import Lookup
import Pretty.Pretty
import Pretty.Terms ()
import Pretty.Types ()
import Syntax.Environment
import Syntax.AST.Types
import Syntax.Common
import TypeInference.Constraints
import TypeTranslation qualified as TT
import Utils
import Data.Map

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

data GenerateReader = GenerateReader { context :: [LinearContext Pos]
                                     }

initialReader :: Environment Inferred -> (Environment Inferred, GenerateReader)
initialReader env = (env, GenerateReader { context = [] })

---------------------------------------------------------------------------------------------
-- GenM
---------------------------------------------------------------------------------------------

newtype GenM a = GenM { getGenM :: ReaderT (Environment Inferred, GenerateReader) (StateT GenerateState (Except Error)) a }
  deriving (Functor, Applicative, Monad, MonadState GenerateState, MonadReader (Environment Inferred, GenerateReader), MonadError Error)

runGenM :: Environment Inferred -> GenM a -> Either Error (a, ConstraintSet)
runGenM env m = case runExcept (runStateT (runReaderT  (getGenM m) (initialReader env)) initialState) of
  Left err -> Left err
  Right (x, state) -> Right (x, constraintSet state)

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
  return (TyVar PosRep Nothing tvar, TyVar NegRep Nothing tvar)

freshTVars :: [(PrdCns, Maybe FreeVarName)] -> GenM (LinearContext Pos, LinearContext Neg)
freshTVars [] = return ([],[])
freshTVars ((Prd,fv):rest) = do
  (lctxtP, lctxtN) <- freshTVars rest
  (tp, tn) <- freshTVar (ProgramVariable (fromMaybeVar fv))
  return (PrdCnsType PrdRep tp:lctxtP, PrdCnsType PrdRep tn:lctxtN)
freshTVars ((Cns,fv):rest) = do
  (lctxtP, lctxtN) <- freshTVars rest
  (tp, tn) <- freshTVar (ProgramVariable (fromMaybeVar fv))
  return (PrdCnsType CnsRep tn:lctxtP, PrdCnsType CnsRep tp:lctxtN)

freshTVarsForTypeParams :: PolarityRep pol -> DataDecl -> GenM ([Typ (FlipPol pol)], [Typ pol], Map TVar (Typ Pos, Typ Neg))
freshTVarsForTypeParams rep dd = do
    let (MkTParams con cov) = data_params dd
    let tn = data_name dd
    con' <- freshTVars tn (fst <$> con)
    cov' <- freshTVars tn (fst <$> cov)
    let map = paramsMap dd (con', cov')
    case rep of
      PosRep -> pure (snd <$> con', fst <$> cov', map)
      NegRep -> pure (fst <$> con', snd <$> cov', map)
  where
    freshTVars ::  TypeName -> [TVar] -> GenM [(Typ Pos, Typ Neg)]
    freshTVars _ [] = pure []
    freshTVars tn (v : vs) = do
      vs' <- freshTVars tn vs
      (tp, tn) <- freshTVar (TypeParameter tn v)
      pure $ (tp, tn) : vs'

    paramsMap :: DataDecl -> ([(Typ Pos, Typ Neg)], [(Typ Pos, Typ Neg)]) -> Map TVar (Typ Pos, Typ Neg)
    paramsMap dd (freshCon, freshCov) =
        let (MkTParams con cov) = data_params dd in
        fromList (zip (fst <$> con) freshCon ++ zip (fst <$> cov) freshCov)

---------------------------------------------------------------------------------------------
-- Running computations in an extended context or environment
---------------------------------------------------------------------------------------------

withContext :: LinearContext 'Pos -> GenM a -> GenM a
withContext ctx m =
  local (\(env,gr@GenerateReader{..}) -> (env, gr { context = ctx:context })) m

---------------------------------------------------------------------------------------------
-- Looking up types in the context and environment
---------------------------------------------------------------------------------------------

-- | Lookup a type of a bound variable in the context.
lookupContext :: PrdCnsRep pc -> Index -> GenM (Typ (PrdCnsToPol pc))
lookupContext rep (i,j) = do
  ctx <- asks (context . snd)
  case indexMaybe ctx i of
    Nothing -> throwGenError ["Bound Variable out of bounds: ", "PrdCns: " <> T.pack (show rep),  "Index: " <> T.pack (show (i,j))]
    Just (lctxt) -> case indexMaybe lctxt j of
      Nothing -> throwGenError ["Bound Variable out of bounds: ", "PrdCns: " <> T.pack (show rep),  "Index: " <> T.pack (show (i,j))]
      Just ty -> case (rep, ty) of
        (PrdRep, PrdCnsType PrdRep ty) -> return ty
        (CnsRep, PrdCnsType CnsRep ty) -> return ty
        (PrdRep, PrdCnsType CnsRep _) -> throwGenError ["Bound Variable " <> T.pack (show (i,j)) <> " was expected to be PrdType, but CnsType was found."]
        (CnsRep, PrdCnsType PrdRep _) -> throwGenError ["Bound Variable " <> T.pack (show (i,j)) <> " was expected to be CnsType, but PrdType was found."]


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
-- Translate nominal types to structural refinement types
---------------------------------------------------------------------------------------------

-- | Recursively translate types in xtor signature to upper bound refinement types
translateXtorSigUpper :: XtorSig Neg -> GenM (XtorSig Neg)
translateXtorSigUpper xts = do
  env <- asks fst
  case TT.translateXtorSigUpper env xts of
    Left err -> throwError err
    Right xts' -> return xts'

-- | Recursively translate a nominal type to an upper bound refinement type
translateTypeUpper :: Typ Neg -> GenM (Typ Neg)
translateTypeUpper ty = do
  env <- asks fst
  case TT.translateTypeUpper env ty of
    Left err -> throwError err
    Right xts' -> return xts'

-- | Recursively translate types in xtor signature to lower bound refinement types
translateXtorSigLower :: XtorSig Pos -> GenM (XtorSig Pos)
translateXtorSigLower xts = do
  env <- asks fst
  case TT.translateXtorSigLower env xts of
    Left err -> throwError err
    Right xts' -> return xts'

-- | Recursively translate a nominal type to a lower bound refinement type
translateTypeLower :: Typ Pos -> GenM (Typ Pos)
translateTypeLower ty = do
  env <- asks fst
  case TT.translateTypeLower env ty of
    Left err -> throwError err
    Right xts' -> return xts'

---------------------------------------------------------------------------------------------
-- Other
---------------------------------------------------------------------------------------------

-- | Specifies whether to infer nominal or refined types
data InferenceMode = InferNominal | InferRefined
  deriving (Eq, Show)

foo :: PrdCnsRep pc -> PolarityRep (PrdCnsToPol pc)
foo PrdRep = PosRep
foo CnsRep = NegRep

fromMaybeVar :: Maybe FreeVarName -> FreeVarName
fromMaybeVar Nothing = MkFreeVarName "generated"
fromMaybeVar (Just fv) = fv

-- | Checks for a given list of XtorNames and a type declaration whether all the xtor names occur in
-- the type declaration (Correctness).
checkCorrectness :: [XtorName]
                 -> DataDecl
                 -> GenM ()
checkCorrectness matched decl = do
  let declared = sig_name <$> fst (data_xtors decl)
  forM_ matched $ \xn -> unless (xn `elem` declared)
    (throwGenError ["Pattern Match Error. The xtor " <> ppPrint xn <> " does not occur in the declaration of type " <> ppPrint (data_name decl)])

-- | Checks for a given list of XtorNames and a type declaration whether all xtors of the type declaration
-- are matched against (Exhaustiveness).
checkExhaustiveness :: [XtorName] -- ^ The xtor names used in the pattern match
                    -> DataDecl   -- ^ The type declaration to check against.
                    -> GenM ()
checkExhaustiveness matched decl = do
  let declared = sig_name <$> fst (data_xtors decl)
  forM_ declared $ \xn -> unless (xn `elem` matched)
    (throwGenError ["Pattern Match Exhaustiveness Error. Xtor: " <> ppPrint xn <> " of type " <>
                     ppPrint (data_name decl) <> " is not matched against." ])
