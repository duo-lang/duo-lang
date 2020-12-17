module SolveConstraints
  ( solveConstraints
  , removeEpsilonEdges
  , removeIslands
  ) where

import Data.Graph.Inductive.Graph

import Control.Monad.State
import Control.Monad.Except
import Data.List ((\\))
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import Syntax.Types
import Syntax.TypeGraph
import Syntax.Terms
import Utils
import Pretty
import TypeAutomata.Determinize (removeEpsilonEdges, removeIslands)

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

data SolverState = SolverState
  { sst_bounds :: Map UVar VariableState
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
subConstraints (SubType (TyVar _) _) = return []
subConstraints (SubType _ (TyVar _)) = return []
-- Data/Data and Codata/Codata constraints
subConstraints cs@(SubType (SimpleType Data xtors1) (SimpleType Data xtors2))
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
subConstraints cs@(SubType (SimpleType Codata xtors1) (SimpleType Codata xtors2))
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
subConstraints (SubType (NominalType tn1) (NominalType tn2)) | tn1 == tn2 = return []
                                                             | otherwise = throwSolverError ("The two nominal types are incompatible: " ++ ppPrint tn1 ++ " and " ++ ppPrint tn2)
-- Data/Codata and Codata/Data Constraints
subConstraints cs@(SubType (SimpleType Data _) (SimpleType Codata _))
  = throwSolverError $  "Constraint: \n      " ++ ppPrint cs ++ "\n is unsolvable. A data type can't be a subtype of a codata type!"
subConstraints cs@(SubType (SimpleType Codata _) (SimpleType Data _))
  = throwSolverError $ "Constraint: \n      " ++ ppPrint cs ++ "\n is unsolvable. A codata type can't be a subtype of a data type!"
-- Nominal/XData and XData/Nominal Constraints
subConstraints (SubType (SimpleType _ _) (NominalType _)) = throwSolverError "Cannot constrain nominal by structural type"
subConstraints (SubType (NominalType _) (SimpleType _ _)) = throwSolverError "Cannot constrain nominal by structural type"

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
        (SubType (TyVar uv) ub) -> do
          modifyBounds (addUpperBound ub) uv
          lbs <- getLowerBounds uv
          let newCss = [SubType lb ub | lb <- lbs]
          solve (newCss ++ css)
        (SubType lb (TyVar uv)) -> do
          modifyBounds (addLowerBound lb) uv
          ubs <- getUpperBounds uv
          let newCss = [SubType lb ub | ub <- ubs]
          solve (newCss ++ css)
        _ -> do
          subCss <- subConstraints cs
          solve (subCss ++ css)

-------------------------------------------------------------------------
-- Translation from SolverState to Type automaton
-------------------------------------------------------------------------

type MkAutM a = State TypeAutEps a

modifyGraph :: (TypeGrEps -> TypeGrEps) -> MkAutM ()
modifyGraph f = modify (\(aut@TypeAut { ta_gr }) -> aut { ta_gr = f ta_gr })

uvarToNodeId :: UVar -> PrdCns -> Node
uvarToNodeId uv Prd = 2 * uvar_id uv
uvarToNodeId uv Cns  = 2 * uvar_id uv + 1

typeToHeadCons :: SimpleType -> HeadCons
typeToHeadCons (TyVar _) = emptyHeadCons
typeToHeadCons (SimpleType s xtors) = singleHeadCons s (S.fromList (map sig_name xtors))
typeToHeadCons (NominalType tn) = emptyHeadCons { hc_nominal = S.singleton tn }

typeToGraph :: PrdCns -> SimpleType -> MkAutM Node
typeToGraph pol (TyVar uv) = return (uvarToNodeId uv pol)
typeToGraph pol ty@(SimpleType s xtors) = do
  newNodeId <- gets (head . newNodes 1 . ta_gr)
  let hc = typeToHeadCons ty
  modifyGraph (insNode (newNodeId, (pol, hc)))
  forM_ xtors $ \(MkXtorSig xt (Twice prdTypes cnsTypes)) -> do
    forM_ (enumerate prdTypes) $ \(i, prdType) -> do
      prdNode <- typeToGraph (applyVariance s Prd pol) prdType
      modifyGraph (insEdge (newNodeId, prdNode, Just (EdgeSymbol s xt Prd i)))
    forM_ (enumerate cnsTypes) $ \(j, cnsType) -> do
      cnsNode <- typeToGraph (applyVariance s Cns pol) cnsType
      modifyGraph (insEdge (newNodeId, cnsNode, Just (EdgeSymbol s xt Cns j)))
  return newNodeId
typeToGraph pol (NominalType tn) = do
  newNodeId <- gets (head . newNodes 1 . ta_gr)
  let hc = emptyHeadCons { hc_nominal = S.singleton tn }
  modifyGraph (insNode (newNodeId, (pol, hc)))
  return newNodeId

-- | Creates upper/lower bounds for a unification variable by inserting epsilon edges into the automaton
insertEpsilonEdges :: UVar -> VariableState -> MkAutM ()
insertEpsilonEdges uv vstate = do
  forM_ [Prd,Cns] $ \pc ->
    forM_ (getBounds pc vstate) $ \ty -> do
      i <- typeToGraph pc ty
      modifyGraph (insEdge (uvarToNodeId uv pc, i, Nothing))

-- | Turns the output of the constraint solver into an automaton by using epsilon-edges to represent lower and upper bounds
solverStateToTypeAutM :: SolverState -> MkAutM ()
solverStateToTypeAutM (SolverState {..}) =
  forM_ (M.toList sst_bounds) (uncurry insertEpsilonEdges)

-- | Creates an initial type automaton from a list of UVars.
mkInitialTypeAut :: [UVar] -> TypeAutEps
mkInitialTypeAut uvs =
  let
    uvNodes = [(uvarToNodeId uv pol, (pol, emptyHeadCons)) | uv <- uvs, pol <- [Prd,Cns]]
    flowEdges = [(uvarToNodeId uv Cns, uvarToNodeId uv Prd) | uv <- uvs]
  in
    TypeAut { ta_gr = mkGraph uvNodes []
            , ta_starts = []
            , ta_flowEdges = flowEdges
            }

-- | Creates the variable states that results from solving constraints.
solveConstraintsOne :: [Constraint] -> [UVar] -> Either Error SolverState
solveConstraintsOne css uvs = do
  let initState = SolverState { sst_bounds = M.fromList [(uv,emptyVarState) | uv <- uvs] , sst_cache = [] }
  (_, solverState) <- runSolverM (solve css) initState
  return solverState

-- | Creates a type automaton from the variable states
solveConstraintsTwo :: SolverState -> TypeAutEps
solveConstraintsTwo solverState =
  let
    initAut = mkInitialTypeAut (M.keys (sst_bounds solverState))
    (_,aut) = runState (solverStateToTypeAutM solverState) initAut
  in
    aut

-- | Takes a given type automaton without a starting state, and adds a simple type as starting state to the automaton.
solveConstraintsThree :: TypeAutEps -> SimpleType -> PrdCns -> TypeAut
solveConstraintsThree aut0 ty pc =
  let
    (start, aut) = runState (typeToGraph pc ty) aut0
  in
    (removeIslands . removeEpsilonEdges) (aut { ta_starts = [start] })

solveConstraints :: [Constraint] -> [UVar] -> SimpleType -> PrdCns -> Either Error TypeAut
solveConstraints css uvs ty pc = do
  solverState <- solveConstraintsOne css uvs
  let aut0 = solveConstraintsTwo solverState
  let aut1 = solveConstraintsThree aut0 ty pc
  return aut1
