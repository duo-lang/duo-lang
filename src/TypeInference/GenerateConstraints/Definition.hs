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
    -- Running computations in extended context or environment.
  , withContext
    -- Instantiating type schemes
  , instantiateTypeScheme
    -- Adding a constraint
  , addConstraint
    -- Other
  , InferenceMode(..)
  , PrdCnsToPol
  , foo
  , prdCnsToPol
  , checkCorrectness
  , checkExhaustiveness
  , translateType
  , translateXtorSig
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Text as T

import Errors
import Lookup
import Pretty.Pretty
import Pretty.STerms ()
import Pretty.ATerms ()
import Pretty.Types ()
import Syntax.ATerms
import Syntax.Program
import Syntax.Types
import qualified TypeTranslation as TT
import Utils

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
                                     , inferMode :: InferenceMode
                                     }

initialReader :: Environment FreeVarName -> InferenceMode -> (Environment FreeVarName, GenerateReader)
initialReader env im = (env, GenerateReader { context = [], inferMode = im })

---------------------------------------------------------------------------------------------
-- GenM
---------------------------------------------------------------------------------------------

newtype GenM a = GenM { getGenM :: ReaderT (Environment FreeVarName, GenerateReader) (StateT GenerateState (Except Error)) a }
  deriving (Functor, Applicative, Monad, MonadState GenerateState, MonadReader (Environment FreeVarName, GenerateReader), MonadError Error)

runGenM :: Environment FreeVarName -> InferenceMode -> GenM a -> Either Error (a, ConstraintSet)
runGenM env im m = case runExcept (runStateT (runReaderT  (getGenM m) (initialReader env im)) initialState) of
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
  local (\(env,gr@GenerateReader{..}) -> (env, gr { context = ctx:context })) m

---------------------------------------------------------------------------------------------
-- Looking up types in the context and environment
---------------------------------------------------------------------------------------------

-- | Lookup a type of a bound variable in the context.
lookupContext :: PrdCnsRep pc -> Index -> GenM (Typ (PrdCnsToPol pc))
lookupContext rep (i,j) = do
  ctx <- asks (context . snd)
  case indexMaybe ctx i of
    Nothing -> throwGenError ["Bound Variable out of bounds: " <> T.pack (show (i,j))]
    Just (MkTypArgs { prdTypes, cnsTypes }) -> case rep of
      PrdRep -> do
        case indexMaybe prdTypes j of
          Nothing -> throwGenError ["Bound Variable out of bounds: " <> T.pack (show (i,j))]
          Just ty -> return ty
      CnsRep -> do
        case indexMaybe cnsTypes j of
          Nothing -> throwGenError ["Bound Variable out of bounds: " <> T.pack (show (i,j))]
          Just ty -> return ty

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

foo :: PrdCnsRep pc -> PolarityRep (PrdCnsToPol pc)
foo PrdRep = PosRep
foo CnsRep = NegRep

-- | Checks for a given list of XtorNames and a type declaration whether all the xtor names occur in
-- the type declaration (Correctness).
checkCorrectness :: [XtorName]
                 -> DataDecl
                 -> GenM ()
checkCorrectness matched decl = do
  let declared = sig_name <$> data_xtors decl PosRep
  forM_ matched $ \xn -> unless (xn `elem` declared) 
    (throwGenError ["Pattern Match Error. The xtor " <> ppPrint xn <> " does not occur in the declaration of type " <> ppPrint (data_name decl)])

-- | Checks for a given list of XtorNames and a type declaration whether all xtors of the type declaration 
-- are matched against (Exhaustiveness).
checkExhaustiveness :: [XtorName] -- ^ The xtor names used in the pattern match
                    -> DataDecl   -- ^ The type declaration to check against.
                    -> GenM ()
checkExhaustiveness matched decl = do
  im <- asks (inferMode . snd)
  -- Only check exhaustiveness when not using refinements
  case im of
    InferRefined -> return ()
    InferNominal -> do
      let declared = sig_name <$> data_xtors decl PosRep
      forM_ declared $ \xn -> unless (xn `elem` matched)
        (throwGenError ["Pattern Match Exhaustiveness Error. Xtor: " <> ppPrint xn <> " of type " <>
          ppPrint (data_name decl) <> " is not matched against." ])

-- | Recursively translate a nominal type to a corresponding structural representation
translateType :: Typ pol -> GenM (Typ pol)
translateType ty = do
  env <- asks fst
  case TT.translateType env ty of
    Left (OtherError err) -> throwGenError [err]
    Left _ -> throwGenError ["Translation of type " <> ppPrint ty <> " failed"]
    Right ty' -> return ty'

-- | Recursively translate an xtor signature
translateXtorSig :: XtorSig pol -> GenM (XtorSig pol)
translateXtorSig xts = do
  env <- asks fst
  case TT.translateXtorSig env xts of
    Left (OtherError err) -> throwGenError [err]
    Left _ -> throwGenError ["Translation of xtor sig " <> ppPrint xts <> " failed"]
    Right xts' -> return xts'