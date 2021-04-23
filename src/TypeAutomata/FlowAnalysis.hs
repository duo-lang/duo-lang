module TypeAutomata.FlowAnalysis
  ( getFlowAnalysisMap
  ) where

import Syntax.Types
import Syntax.TypeAutomaton

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree

import Control.Monad.State

import Data.List (intersect, maximumBy)
import Data.Ord (comparing)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

-------------------------------------------------------------------------------------
-- Flow analysis
-------------------------------------------------------------------------------------

type FlowGraph = Gr () ()

-- | Generate a graph consisting only of the flow_edges of the type automaton.
genFlowGraph :: TypeAut' EdgeLabelNormal f pol -> FlowGraph
genFlowGraph TypeAut{..} = mkGraph [(n,()) | n <- nodes ta_gr] [(i,j,()) | (i,j) <- ta_flowEdges]

flowComponent :: FlowGraph -> Node -> [Node]
flowComponent flgr i =
  let
    ns = neighbors flgr i
  in
    if null ns
      then [i]
      else ns ++ (foldr1 intersect) (map (neighbors flgr) ns)

freshTVar :: State Int TVar
freshTVar = do
  n <- get
  modify (+1)
  return (MkTVar ("t" ++ show n))

flowAnalysisState :: FlowGraph -> State Int (Map Node (Set TVar))
flowAnalysisState flgr =
    let
      nextNode = maximumBy (comparing (length . flowComponent flgr)) (nodes flgr)
      comp = flowComponent flgr nextNode
      newGr = delEdges [(x,y) | (x,y) <- edges flgr, x `elem` comp, y `elem` comp] flgr
    in
      if length comp < 2
        then return (M.fromList [(n,S.empty) | n <- nodes flgr])
        else do
          tv <- freshTVar
          rest <- flowAnalysisState newGr
          return $ foldr (.) id (map (M.adjust (S.insert tv)) comp) rest

getFlowAnalysisMap :: TypeAut' EdgeLabelNormal f pol -> Map Node (Set TVar)
getFlowAnalysisMap aut = fst $ runState (flowAnalysisState (genFlowGraph aut)) 0
