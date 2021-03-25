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
  , constraints :: [Constraint]
  }

initialState :: GenerateState
initialState = GenerateState { varCount = 0, constraints = [] }

-- | After constraint generation is finished, we can turn the final state into a ConstraintSet.
stateToConstraintSet :: GenerateState -> ConstraintSet
stateToConstraintSet GenerateState {..} = ConstraintSet
  { cs_constraints = constraints
  , cs_uvars = (\i -> MkTVar (show i)) <$> [0..varCount]
  }

---------------------------------------------------------------------------------------------
-- Reader of GenM
--
-- We have access to a program environment and a local variable context.
---------------------------------------------------------------------------------------------

data GenerateReader bs = GenerateReader { context :: [TypArgs Pos]
                                        , env :: Environment bs
                                        }

initialReader :: Environment bs -> GenerateReader bs
initialReader env = GenerateReader { context = []
                                   , env = env
                                   }

---------------------------------------------------------------------------------------------
-- GenM
---------------------------------------------------------------------------------------------

type GenM bs a = ReaderT (GenerateReader bs) (StateT GenerateState (Except Error)) a

runGenM :: Environment bs -> GenM bs a -> Either Error (a, ConstraintSet)
runGenM env m = case runExcept (runStateT (runReaderT  m (initialReader env)) initialState) of
  Left err -> Left err
  Right (x, state) -> Right (x, stateToConstraintSet state)

---------------------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------------------

throwGenError :: String -> GenM bs a
throwGenError msg = throwError $ GenConstraintsError msg

-- | Generate a fresh type variable.
freshTVar :: GenM bs (Typ Pos, Typ Neg)
freshTVar = do
  var <- gets varCount
  modify (\gs@GenerateState{} -> gs { varCount = var + 1 })
  return (TyVar PosRep Normal (MkTVar (show var))
         ,TyVar NegRep Normal (MkTVar (show var)))

freshTVars :: Twice [bs] -> GenM bs (TypArgs Pos, TypArgs Neg)
freshTVars (Twice prdArgs cnsArgs) = do
  (prdArgsPos, prdArgsNeg) <- unzip <$> forM prdArgs (\_ -> freshTVar)
  (cnsArgsPos, cnsArgsNeg) <- unzip <$> forM cnsArgs (\_ -> freshTVar)
  return (MkTypArgs prdArgsPos cnsArgsNeg, MkTypArgs prdArgsNeg cnsArgsPos)


instantiateTypeScheme :: TypeScheme pol -> GenM bs (Typ pol)
instantiateTypeScheme TypeScheme { ts_vars, ts_monotype } = do
  freshVars <- forM ts_vars (\tv -> freshTVar >>= \ty -> return (tv, ty))
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
lookupType :: PrdCnsRep pc -> Index -> GenM bs (Typ (PrdCnsToPol pc))
lookupType PrdRep (i,j) = do
  ctx <- asks context
  let (MkTypArgs { prdTypes }) = ctx !! i
  return $ prdTypes !! j
lookupType CnsRep (i,j) = do
  ctx <- asks context
  let (MkTypArgs { cnsTypes }) = ctx !! i
  return $ cnsTypes !! j

-- | Add a constraint to the state.
addConstraint :: Constraint -> GenM bs ()
addConstraint c = modify (\gs@GenerateState { constraints } -> gs { constraints = c:constraints })

lookupCase :: XtorName -> GenM bs (TypArgs Pos, XtorArgs bs)
lookupCase xt = do
  env <- asks env
  case M.lookup xt (P.envToXtorMap env) of
    Nothing -> throwGenError $ "GenerateConstraints: The xtor " ++ ppPrint xt ++ " could not be looked up."
    Just types@(MkTypArgs prdTypes cnsTypes) -> do
      let prds = (\_ -> FreeVar PrdRep "y") <$> prdTypes
      let cnss = (\_ -> FreeVar CnsRep "y") <$> cnsTypes
      return (types, MkXtorArgs prds cnss)

lookupXtor :: XtorName -> GenM bs DataDecl
lookupXtor xt = do
  env <- asks env
  case P.lookupXtor xt env of
    Nothing -> throwGenError $ "Constructor " ++ ppPrint xt ++ " is not contained in program"
    Just decl -> return decl
