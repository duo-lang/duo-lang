module BoundsToAutomaton
  ( solverStateToTypeAut
  ) where

import Data.Graph.Inductive.Graph

import Control.Monad.State
import qualified Data.Set as S
import qualified Data.Map as M
import Data.Void

import SolveConstraints
import Syntax.Types
import Syntax.TypeGraph
import Syntax.Terms
import Utils
import TypeAutomata.Determinize (removeEpsilonEdges, removeIslands)

-------------------------------------------------------------------------
-- Translation from SolverState to Type automaton
-------------------------------------------------------------------------

type MkAutM a = State TypeAutEps a

modifyGraph :: (TypeGrEps -> TypeGrEps) -> MkAutM ()
modifyGraph f = modify (\(aut@TypeAut { ta_gr }) -> aut { ta_gr = f ta_gr })

uvarToNodeId :: UVar -> PrdCns -> Node
uvarToNodeId uv Prd = 2 * uvar_id uv
uvarToNodeId uv Cns  = 2 * uvar_id uv + 1

getBounds :: PrdCns -> VariableState -> [SimpleType]
getBounds Prd = vst_lowerbounds
getBounds Cns = vst_upperbounds


typeToHeadCons :: SimpleType -> HeadCons
typeToHeadCons (TyUVar () _) = emptyHeadCons
typeToHeadCons (TySimple s xtors) = singleHeadCons s (S.fromList (map sig_name xtors))
typeToHeadCons (TyNominal tn) = emptyHeadCons { hc_nominal = S.singleton tn }
typeToHeadCons (TyTVar v _ _) = absurd v
typeToHeadCons (TySet v _ _) = absurd v
typeToHeadCons (TyRec v _ _) = absurd v

typeToGraph :: PrdCns -> SimpleType -> MkAutM Node
typeToGraph pol (TyUVar () uv) = return (uvarToNodeId uv pol)
typeToGraph pol ty@(TySimple s xtors) = do
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
typeToGraph pol (TyNominal tn) = do
  newNodeId <- gets (head . newNodes 1 . ta_gr)
  let hc = emptyHeadCons { hc_nominal = S.singleton tn }
  modifyGraph (insNode (newNodeId, (pol, hc)))
  return newNodeId
typeToGraph _ (TyTVar v _ _) = absurd v
typeToGraph _ (TySet v _ _) = absurd v
typeToGraph _ (TyRec v _ _) = absurd v

-- | Creates upper/lower bounds for a unification variable by inserting epsilon edges into the automaton
insertEpsilonEdges :: UVar -> VariableState -> MkAutM ()
insertEpsilonEdges uv vstate = do
  forM_ [Prd,Cns] $ \pc ->
    forM_ (getBounds pc vstate) $ \ty -> do
      i <- typeToGraph pc ty
      modifyGraph (insEdge (uvarToNodeId uv pc, i, Nothing))

-- | Turns the output of the constraint solver into an automaton by using epsilon-edges to represent lower and upper bounds
solverStateToTypeAutM :: SolverResult -> MkAutM ()
solverStateToTypeAutM solverResult =
  forM_ (M.toList solverResult) (uncurry insertEpsilonEdges)

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



-- | Creates a type automaton from the variable states
solveConstraintsTwo :: SolverResult -> TypeAutEps
solveConstraintsTwo solverResult =
  let
    initAut = mkInitialTypeAut (M.keys solverResult)
    (_,aut) = runState (solverStateToTypeAutM solverResult) initAut
  in
    aut

-- | Takes a given type automaton without a starting state, and adds a simple type as starting state to the automaton.
solveConstraintsThree :: TypeAutEps -> SimpleType -> PrdCns -> TypeAut
solveConstraintsThree aut0 ty pc =
  let
    (start, aut) = runState (typeToGraph pc ty) aut0
  in
    (removeIslands . removeEpsilonEdges) (aut { ta_starts = [start] })

solverStateToTypeAut :: SolverResult -> SimpleType -> PrdCns -> Either Error TypeAut
solverStateToTypeAut solverState ty pc = do
  let aut0 = solveConstraintsTwo solverState
  let aut1 = solveConstraintsThree aut0 ty pc
  return aut1


