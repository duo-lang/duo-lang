module SolveConstraints
  ( VariableState(..)
  , SolverResult
  , solveConstraints
  ) where

import Control.Monad.State
import Control.Monad.Except
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Void

import Syntax.Types
import Utils
import Pretty

------------------------------------------------------------------------------
-- VariableState and SolverResult
------------------------------------------------------------------------------

data VariableState = VariableState
  { vst_upperbounds :: [SimpleType]
  , vst_lowerbounds :: [SimpleType] }

emptyVarState :: VariableState
emptyVarState = VariableState [] []

type SolverResult = Map UVar VariableState

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

modifyBounds :: (VariableState -> VariableState) -> UVar -> SolverM ()
modifyBounds f uv = modify (\(SolverState varMap cache) -> SolverState (M.adjust f uv varMap) cache)

addUpperBound :: UVar -> SimpleType -> SolverM [Constraint]
addUpperBound uv ty = do
  modifyBounds (\(VariableState ubs lbs) -> VariableState (ty:ubs) lbs)uv
  lbs <- gets (vst_lowerbounds . (M.! uv) . sst_bounds)
  return [SubType lb ty | lb <- lbs]

addLowerBound :: UVar -> SimpleType -> SolverM [Constraint]
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
        (SubType (TyUVar () uv) ub) -> do
          newCss <- addUpperBound uv ub
          solve (newCss ++ css)
        (SubType lb (TyUVar () uv)) -> do
          newCss <- addLowerBound uv lb
          solve (newCss ++ css)
        _ -> do
          subCss <- subConstraints cs
          solve (subCss ++ css)

subConstraints :: Constraint -> SolverM [Constraint]
-- Data/Data and Codata/Codata constraints
subConstraints cs@(SubType (TySimple Data xtors1) (TySimple Data xtors2)) = do
  let foo = (map sig_name xtors1) \\ (map sig_name xtors2)
  if not . null $ foo
    then throwSolverError [ "Constraint:"
                          , ppPrint cs
                          , "is unsolvable, because xtor:"
                          , ppPrint (head foo)
                          , "occurs only in the left side." ]
    else return $ do -- list monad
      (MkXtorSig xtName (Twice prd1 cns1)) <- xtors1
      let Just (Twice prd2 cns2) = lookup xtName ((\(MkXtorSig xt args) -> (xt, args)) <$> xtors2) --safe, because of check above
      zipWith SubType prd1 prd2 ++ zipWith SubType cns2 cns1
subConstraints cs@(SubType (TySimple Codata xtors1) (TySimple Codata xtors2)) = do
  let foo = (map sig_name xtors2) \\ (map sig_name xtors1)
  if not . null $ foo
    then throwSolverError [ "Constraint:"
                          , ppPrint cs
                          , "is unsolvable, because xtor:"
                          , ppPrint (head foo)
                          , "occurs only in the left side." ]
    else return $ do -- list monad
      (MkXtorSig xtName (Twice prd2 cns2)) <- xtors2
      let Just (Twice prd1 cns1) = lookup xtName ((\(MkXtorSig xt args) -> (xt, args)) <$> xtors1) --safe, because of check above
      zipWith SubType prd2 prd1 ++ zipWith SubType cns1 cns2
-- Nominal/Nominal Constraint
subConstraints (SubType (TyNominal tn1) (TyNominal tn2)) | tn1 == tn2 = return []
                                                         | otherwise = throwSolverError ["The two nominal types are incompatible: " ++ ppPrint tn1 ++ " and " ++ ppPrint tn2]
-- Data/Codata and Codata/Data Constraints
subConstraints cs@(SubType (TySimple Data _) (TySimple Codata _))
  = throwSolverError [ "Constraint:"
                     , "     " ++ ppPrint cs
                     , "is unsolvable. A data type can't be a subtype of a codata type!" ]
subConstraints cs@(SubType (TySimple Codata _) (TySimple Data _))
  = throwSolverError [ "Constraint:"
                     , "     "++ ppPrint cs
                     , "is unsolvable. A codata type can't be a subtype of a data type!" ]
-- Nominal/XData and XData/Nominal Constraints
subConstraints (SubType (TySimple _ _) (TyNominal _)) = throwSolverError ["Cannot constrain nominal by structural type"]
subConstraints (SubType (TyNominal _) (TySimple _ _)) = throwSolverError ["Cannot constrain nominal by structural type"]
-- subConstraints should never be called if the upper or lower bound is a unification variable.
subConstraints (SubType (TyUVar () _) _) = throwSolverError ["subConstraints should only be called if neither upper nor lower bound are unification variables"]
subConstraints (SubType _ (TyUVar () _)) = throwSolverError ["subConstraints should only be called if neither upper nor lower bound are unification variables"]
-- Impossible constructors. Constraints must be between simple types.
subConstraints (SubType (TyTVar v _ _) _) = absurd v
subConstraints (SubType _ (TyTVar v _ _)) = absurd v
subConstraints (SubType (TySet v _ _) _)  = absurd v
subConstraints (SubType _ (TySet v _ _))  = absurd v
subConstraints (SubType (TyRec v _ _) _)  = absurd v
subConstraints (SubType _ (TyRec v _ _))  = absurd v

------------------------------------------------------------------------------
-- Exported Function
------------------------------------------------------------------------------

-- | Creates the variable states that results from solving constraints.
solveConstraints :: ConstraintSet -> Either Error SolverResult
solveConstraints constraintSet@(ConstraintSet css _) = do
  (_, solverState) <- runSolverM (solve css) (createInitState constraintSet)
  return (sst_bounds solverState)

