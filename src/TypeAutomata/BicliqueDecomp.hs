module TypeAutomata.BicliqueDecomp
  ( FlowGraph
  , foo
  ) where

import Control.Monad.State
    ( MonadState(get), evalState, State, modify )
import Data.List (intersect, maximumBy)
import Data.Ord (comparing)
import Data.Graph.Inductive.PatriciaTree

import Data.Set (Set)
import Data.Set qualified as S
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T

import Data.Graph.Inductive.Graph

import Syntax.Types

-------------------------------------------------------------------------------------
-- Flow analysis
-------------------------------------------------------------------------------------

type FlowGraph = Gr () ()

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
  return (MkTVar ("t" <> T.pack (show n)))

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

foo :: FlowGraph -> Map Node (Set TVar)
foo flgr = evalState (flowAnalysisState flgr) 0
