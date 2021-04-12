module TypeInference.GenerateConstraints.Definition where

import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State


import Pretty.Pretty
import Syntax.ATerms
import Syntax.STerms
import Syntax.Types
import Syntax.Program (Environment)
import qualified Syntax.Program as P
import Utils

---------------------------------------------------------------------------------------------
-- State of GenM
--
-- We use varCount for generating fresh type variables, and collect the constraints.
---------------------------------------------------------------------------------------------

data GenerateState = GenerateState
  { varCount :: Int
  , constraintSet :: ConstraintSet
  }

initialState :: GenerateState
initialState = GenerateState { varCount = 0
                             , constraintSet = ConstraintSet { cs_constraints = []
                                                             , cs_uvars = []
                                                             }
                             }

-- | After constraint generation is finished, we can turn the final state into a ConstraintSet.
stateToConstraintSet :: GenerateState -> ConstraintSet
stateToConstraintSet GenerateState { constraintSet } = constraintSet

---------------------------------------------------------------------------------------------
-- Reader of GenM
--
-- We have access to a program environment and a local variable context.
---------------------------------------------------------------------------------------------

data GenerateReader = GenerateReader { context :: [TypArgs Pos]
                                     , env :: Environment FreeVarName
                                     }

initialReader :: Environment FreeVarName -> GenerateReader
initialReader env = GenerateReader { context = []
                                   , env = env
                                   }

---------------------------------------------------------------------------------------------
-- GenM
---------------------------------------------------------------------------------------------

type GenM a = ReaderT GenerateReader (StateT GenerateState (Except Error)) a

runGenM :: Environment FreeVarName -> GenM a -> Either Error (a, ConstraintSet)
runGenM env m = case runExcept (runStateT (runReaderT  m (initialReader env)) initialState) of
  Left err -> Left err
  Right (x, state) -> Right (x, stateToConstraintSet state)

---------------------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------------------

throwGenError :: String -> GenM a
throwGenError msg = throwError $ GenConstraintsError msg

-- | Generate a fresh type variable.
freshTVar :: UVarProvenance -> GenM (Typ Pos, Typ Neg)
freshTVar uvp = do
  var <- gets varCount
  let tvar = MkTVar ("u" <> (show var))
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


instantiateTypeScheme :: TypeScheme pol -> GenM (Typ pol)
instantiateTypeScheme TypeScheme { ts_vars, ts_monotype } = do
  freshVars <- forM ts_vars (\tv -> freshTVar (Other "TypeScheme instantiation") >>= \ty -> return (tv, ty))
  return $ substituteType (M.fromList freshVars) ts_monotype

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

-- | Lookup a type of a bound variable in the context.
lookupType :: PrdCnsRep pc -> Index -> GenM (Typ (PrdCnsToPol pc))
lookupType rep (i,j) = do
  ctx <- asks context
  case indexMaybe ctx i of
    Nothing -> throwGenError $ "Bound Variable out of bounds: " ++ show (i,j)
    Just (MkTypArgs { prdTypes, cnsTypes }) -> case rep of
      PrdRep -> do
        case indexMaybe prdTypes j of
          Nothing -> throwGenError $ "Bound Variable out of bounds: " ++ show (i,j)
          Just ty -> return ty
      CnsRep -> do
        case indexMaybe cnsTypes j of
          Nothing -> throwGenError $ "Bound Variable out of bounds: " ++ show (i,j)
          Just ty -> return ty

-- | Add a constraint to the state.
addConstraint :: Constraint ConstraintInfo -> GenM ()
addConstraint c = modify foo
  where
    foo gs@GenerateState { constraintSet } = gs { constraintSet = bar constraintSet }
    bar cs@ConstraintSet { cs_constraints } = cs { cs_constraints = c:cs_constraints }

lookupCase :: XtorName -> GenM (TypArgs Pos, XtorArgs () FreeVarName)
lookupCase xt = do
  env <- asks env
  case M.lookup xt (P.envToXtorMap env) of
    Nothing -> throwGenError $ "GenerateConstraints: The xtor " ++ ppPrint xt ++ " could not be looked up."
    Just types@(MkTypArgs prdTypes cnsTypes) -> do
      let prds = (\_ -> FreeVar () PrdRep "y") <$> prdTypes
      let cnss = (\_ -> FreeVar () CnsRep "y") <$> cnsTypes
      return (types, MkXtorArgs prds cnss)

lookupXtor :: XtorName -> GenM DataDecl
lookupXtor xt = do
  env <- asks env
  case P.lookupXtor xt env of
    Nothing -> throwGenError $ "Constructor " ++ ppPrint xt ++ " is not contained in program"
    Just decl -> return decl
