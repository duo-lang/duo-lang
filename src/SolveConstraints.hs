module SolveConstraints
  ( solveConstraints
  , SolverResult
  , VariableState(..)
  , getBounds
  ) where

import Control.Monad.State
import Control.Monad.Except
import Data.List ((\\))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Void

import Syntax.Types
import Syntax.Terms
import Utils
import Pretty

data VariableState = VariableState
  { vst_upperbounds :: [SimpleType]
  , vst_lowerbounds :: [SimpleType] }


emptyVarState :: VariableState
emptyVarState = VariableState [] []

getBounds :: PrdCns -> VariableState -> [SimpleType]
getBounds Prd = vst_lowerbounds
getBounds Cns = vst_upperbounds

addUpperBound :: SimpleType -> VariableState -> VariableState
addUpperBound bound (VariableState ubs lbs) = VariableState (bound:ubs) lbs

addLowerBound :: SimpleType -> VariableState -> VariableState
addLowerBound bound (VariableState ubs lbs) = VariableState ubs (bound:lbs)

type SolverResult = Map UVar VariableState

data SolverState = SolverState
  { sst_bounds :: SolverResult
  , sst_cache :: [Constraint] }

type SolverM a = (StateT SolverState (Except Error)) a

runSolverM :: SolverM a -> SolverState -> Either Error (a, SolverState)
runSolverM m initSt = runExcept (runStateT m initSt)

throwSolverError :: String -> SolverM a
throwSolverError = throwError . SolveConstraintsError

modifyCache :: ([Constraint] -> [Constraint]) -> SolverM ()
modifyCache f = modify (\(SolverState gr cache) -> SolverState gr (f cache))

modifyBounds :: (VariableState -> VariableState) -> UVar -> SolverM ()
modifyBounds f uv = modify (\(SolverState varMap cache) -> SolverState (M.adjust f uv varMap) cache)

getUpperBounds :: UVar -> SolverM [SimpleType]
getUpperBounds uv = gets (vst_upperbounds . (M.! uv) . sst_bounds)

getLowerBounds :: UVar -> SolverM [SimpleType]
getLowerBounds uv = gets (vst_lowerbounds . (M.! uv) . sst_bounds)

subConstraints :: Constraint -> SolverM [Constraint]
-- Atomic constraints (one side is a TyVar)
subConstraints (SubType (TyUVar () _) _) = return []
subConstraints (SubType _ (TyUVar () _)) = return []
-- Data/Data and Codata/Codata constraints
subConstraints cs@(SubType (TySimple Data xtors1) (TySimple Data xtors2))
  = if not . null $ (map sig_name xtors1) \\ (map sig_name xtors2)
    then throwSolverError $ unlines [ "Constraint:"
                                    , ppPrint cs
                                    , "is unsolvable, because xtor:"
                                    , ppPrint (head $ (map sig_name xtors1) \\ (map sig_name xtors2))
                                    , "occurs only in the left side." ]
    else return $ do -- list monad
      (MkXtorSig xtName (Twice prd1 cns1)) <- xtors1
      let Just (Twice prd2 cns2) = lookup xtName ((\(MkXtorSig xt args) -> (xt, args)) <$> xtors2) --safe, because of check above
      zipWith SubType prd1 prd2 ++ zipWith SubType cns2 cns1
subConstraints cs@(SubType (TySimple Codata xtors1) (TySimple Codata xtors2))
  = if not . null $ (map sig_name xtors2) \\ (map sig_name xtors1)
    then throwSolverError $ unlines [ "Constraint:"
                                    , ppPrint cs
                                    , "is unsolvable, because xtor:"
                                    , ppPrint (head $ (map sig_name xtors2) \\ (map sig_name xtors1))
                                    , "occurs only in the left side." ]
    else return $ do -- list monad
      (MkXtorSig xtName (Twice prd2 cns2)) <- xtors2
      let Just (Twice prd1 cns1) = lookup xtName ((\(MkXtorSig xt args) -> (xt, args)) <$> xtors1) --safe, because of check above
      zipWith SubType prd2 prd1 ++ zipWith SubType cns1 cns2
-- Nominal/Nominal Constraint
subConstraints (SubType (TyNominal tn1) (TyNominal tn2)) | tn1 == tn2 = return []
                                                             | otherwise = throwSolverError ("The two nominal types are incompatible: " ++ ppPrint tn1 ++ " and " ++ ppPrint tn2)
-- Data/Codata and Codata/Data Constraints
subConstraints cs@(SubType (TySimple Data _) (TySimple Codata _))
  = throwSolverError $  "Constraint: \n      " ++ ppPrint cs ++ "\n is unsolvable. A data type can't be a subtype of a codata type!"
subConstraints cs@(SubType (TySimple Codata _) (TySimple Data _))
  = throwSolverError $ "Constraint: \n      " ++ ppPrint cs ++ "\n is unsolvable. A codata type can't be a subtype of a data type!"
-- Nominal/XData and XData/Nominal Constraints
subConstraints (SubType (TySimple _ _) (TyNominal _)) = throwSolverError "Cannot constrain nominal by structural type"
subConstraints (SubType (TyNominal _) (TySimple _ _)) = throwSolverError "Cannot constrain nominal by structural type"
-- Impossible constructors
subConstraints (SubType (TyTVar v _ _) _) = absurd v
subConstraints (SubType _ (TyTVar v _ _)) = absurd v
subConstraints (SubType (TySet v _ _) _) = absurd v
subConstraints (SubType _ (TySet v _ _)) = absurd v
subConstraints (SubType (TyRec v _ _) _) = absurd v
subConstraints (SubType _ (TyRec v _ _)) = absurd v

--subConstraints _ = return [] -- constraint is atomic

solve :: [Constraint] -> SolverM ()
solve [] = return ()
solve (cs:css) = do
  cache <- gets sst_cache
  if cs `elem` cache
    then solve css
    else do
      modifyCache (cs:)
      case cs of
        (SubType (TyUVar () uv) ub) -> do
          modifyBounds (addUpperBound ub) uv
          lbs <- getLowerBounds uv
          let newCss = [SubType lb ub | lb <- lbs]
          solve (newCss ++ css)
        (SubType lb (TyUVar () uv)) -> do
          modifyBounds (addLowerBound lb) uv
          ubs <- getUpperBounds uv
          let newCss = [SubType lb ub | ub <- ubs]
          solve (newCss ++ css)
        _ -> do
          subCss <- subConstraints cs
          solve (subCss ++ css)



-- | Creates the variable states that results from solving constraints.
solveConstraints :: [Constraint] -> [UVar] -> Either Error SolverResult
solveConstraints css uvs = do
  let initState = SolverState { sst_bounds = M.fromList [(uv,emptyVarState) | uv <- uvs] , sst_cache = [] }
  (_, solverState) <- runSolverM (solve css) initState
  return (sst_bounds solverState)

