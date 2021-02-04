module TypeInference.SolveConstraints
  ( VariableState(..)
  , SolverResult
  , solveConstraints
  ) where

import Control.Monad.State
import Control.Monad.Except
import Data.List (find)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Syntax.Types
import Syntax.CommonTerm (XtorName)
import Utils
import Pretty.Pretty

------------------------------------------------------------------------------
-- VariableState and SolverResult
------------------------------------------------------------------------------

data VariableState = VariableState
  { vst_upperbounds :: [Typ Pos]
  , vst_lowerbounds :: [Typ Pos] }

emptyVarState :: VariableState
emptyVarState = VariableState [] []

type SolverResult = Map TVar VariableState

------------------------------------------------------------------------------
-- Constraint solver monad
------------------------------------------------------------------------------

data SolverState = SolverState
  { sst_bounds :: SolverResult
  , sst_cache :: Set Constraint }

createInitState :: ConstraintSet -> SolverState
createInitState (ConstraintSet _ uvs) = SolverState { sst_bounds = M.fromList [(uv,emptyVarState) | uv <- uvs]
                                                    , sst_cache = S.empty }

type SolverM a = (StateT SolverState (Except Error)) a

runSolverM :: SolverM a -> SolverState -> Either Error (a, SolverState)
runSolverM m initSt = runExcept (runStateT m initSt)

------------------------------------------------------------------------------
-- Monadic helper functions
------------------------------------------------------------------------------

throwSolverError :: [String] -> SolverM a
throwSolverError = throwError . SolveConstraintsError . unlines

addToCache :: Constraint -> SolverM ()
addToCache cs = modifyCache (S.insert cs)
  where
    modifyCache :: (Set Constraint -> Set Constraint) -> SolverM ()
    modifyCache f = modify (\(SolverState gr cache) -> SolverState gr (f cache))

inCache :: Constraint -> SolverM Bool
inCache cs = gets sst_cache >>= \cache -> pure (cs `elem` cache)

modifyBounds :: (VariableState -> VariableState) -> TVar -> SolverM ()
modifyBounds f uv = modify (\(SolverState varMap cache) -> SolverState (M.adjust f uv varMap) cache)

addUpperBound :: TVar -> Typ Pos -> SolverM [Constraint]
addUpperBound uv ty = do
  modifyBounds (\(VariableState ubs lbs) -> VariableState (ty:ubs) lbs)uv
  lbs <- gets (vst_lowerbounds . (M.! uv) . sst_bounds)
  return [SubType lb ty | lb <- lbs]

addLowerBound :: TVar -> Typ Pos -> SolverM [Constraint]
addLowerBound uv ty = do
  modifyBounds (\(VariableState ubs lbs) -> VariableState ubs (ty:lbs)) uv
  ubs <- gets (vst_upperbounds . (M.! uv) . sst_bounds)
  return [SubType ty ub | ub <- ubs]

------------------------------------------------------------------------------
-- Constraint solving algorithm
------------------------------------------------------------------------------

solve :: [Constraint] -> SolverM ()
solve [] = return ()
solve (cs:css) = do
  cacheHit <- inCache cs
  case cacheHit of
    True -> solve css
    False -> do
      addToCache cs
      case cs of
        (SubType (TyVar Normal uv) ub) -> do
          newCss <- addUpperBound uv ub
          solve (newCss ++ css)
        (SubType lb (TyVar Normal uv)) -> do
          newCss <- addLowerBound uv lb
          solve (newCss ++ css)
        _ -> do
          subCss <- subConstraints cs
          solve (subCss ++ css)

lookupXtor :: XtorName -> [XtorSig Pos] -> SolverM (XtorSig Pos)
lookupXtor xtName xtors = case find (\(MkXtorSig xtName' _) -> xtName == xtName') xtors of
  Nothing -> throwSolverError ["The xtor"
                              , ppPrint xtName
                              , "is not contained in the list of xtors"
                              , ppPrint xtors ]
  Just xtorSig -> pure xtorSig

checkXtor :: [XtorSig Pos] -> XtorSig Pos ->  SolverM [Constraint]
checkXtor xtors2 (MkXtorSig xtName (MkTypArgs prd1 cns1)) = do
  MkXtorSig _ (MkTypArgs prd2 cns2) <- lookupXtor xtName xtors2
  pure $ zipWith SubType prd1 prd2 ++ zipWith SubType cns2 cns1

subConstraints :: Constraint -> SolverM [Constraint]
-- Set constraints
subConstraints (SubType (TySet Union tys) ty)  = return [SubType ty' ty | ty' <- tys]
subConstraints (SubType (TySet Inter _) _)  = error "Cannot occur if types are polarized"
subConstraints (SubType ty (TySet Inter tys))  = return [SubType ty ty' | ty' <- tys]
subConstraints (SubType _ (TySet Union _))  = error "Cannot occur if types are polarized"
-- Recursive constraints
subConstraints (SubType (TyRec _tv _ty) ty')  = return [SubType (error "TODO: implement unrolling of rec type") ty']
subConstraints (SubType ty' (TyRec _tv _ty))  = return [SubType ty' (error "TODO: implement unrolling of rec type")]
-- Data/Data and Codata/Codata constraints
subConstraints (SubType (TyStructural Data xtors1) (TyStructural Data xtors2)) = do
  constraints <- forM xtors1 (checkXtor xtors2)
  pure $ concat constraints
subConstraints (SubType (TyStructural Codata xtors1) (TyStructural Codata xtors2)) = do
  constraints <- forM xtors2 (checkXtor xtors1)
  pure $ concat constraints
-- Nominal/Nominal Constraint
subConstraints (SubType (TyNominal tn1) (TyNominal tn2)) | tn1 == tn2 = return []
                                                         | otherwise = throwSolverError ["The following nominal types are incompatible:"
                                                                                        , "    " ++ ppPrint tn1
                                                                                        , "and"
                                                                                        , "    " ++ ppPrint tn2 ]
-- Data/Codata and Codata/Data Constraints
subConstraints cs@(SubType (TyStructural Data _) (TyStructural Codata _))
  = throwSolverError [ "Constraint:"
                     , "     " ++ ppPrint cs
                     , "is unsolvable. A data type can't be a subtype of a codata type!" ]
subConstraints cs@(SubType (TyStructural Codata _) (TyStructural Data _))
  = throwSolverError [ "Constraint:"
                     , "     "++ ppPrint cs
                     , "is unsolvable. A codata type can't be a subtype of a data type!" ]
-- Nominal/XData and XData/Nominal Constraints
subConstraints (SubType (TyStructural _ _) (TyNominal _)) = throwSolverError ["Cannot constrain nominal by structural type"]
subConstraints (SubType (TyNominal _) (TyStructural _ _)) = throwSolverError ["Cannot constrain nominal by structural type"]
-- subConstraints should never be called if the upper or lower bound is a unification variable.
subConstraints (SubType (TyVar _ _) _) =
  throwSolverError ["subConstraints should only be called if neither upper nor lower bound are unification variables"]
subConstraints (SubType _ (TyVar _ _)) =
  throwSolverError ["subConstraints should only be called if neither upper nor lower bound are unification variables"]

------------------------------------------------------------------------------
-- Exported Function
------------------------------------------------------------------------------

-- | Creates the variable states that results from solving constraints.
solveConstraints :: ConstraintSet -> Either Error SolverResult
solveConstraints constraintSet@(ConstraintSet css _) = do
  (_, solverState) <- runSolverM (solve css) (createInitState constraintSet)
  return (sst_bounds solverState)

