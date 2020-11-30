module TypeAutomata.FlowAnalysis
  ( genFlowGraph
  , removeAdmissableFlowEdges
  , getFlowAnalysisMap
  ) where

import Syntax.Terms
import Syntax.Types
import Syntax.TypeGraph

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree

import Control.Applicative ((<|>))
import Control.Monad.State

import Data.List (intersect, maximumBy, delete)
import Data.Ord (comparing)
import Data.Tuple (swap)
import Data.Maybe (isJust)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

----------------------------------------------------------------------------------------
-- Flow edge admissability check
----------------------------------------------------------------------------------------

sucWith :: (DynGraph gr, Eq b) => gr a b -> Node -> b -> Maybe Node
sucWith gr i el = lookup el (map swap (lsuc gr i))

-- this version of admissability check also accepts if the edge under consideration is in the set of known flow edges
-- needs to be seperated for technical reasons...
admissable :: TypeAutDet -> FlowEdge -> Bool
admissable aut@TypeAut {..} e = isJust $ admissableM (aut { ta_flowEdges = delete e ta_flowEdges }) e

admissableM :: TypeAutDet -> FlowEdge -> Maybe ()
admissableM aut@TypeAut{..} e@(i,j) =
    let
      subtypeData = do -- Maybe monad
        (Neg, HeadCons (Just dat1) _) <- lab ta_gr i
        (Pos, HeadCons (Just dat2) _) <- lab ta_gr j
        _ <- forM (S.toList dat1) $ \xt -> guard (xt `S.member` dat2)
        _ <- forM (S.toList dat1) $ \xt -> do
          _ <- forM [(n,el) | (n, el@(EdgeSymbol Data xt' Prd _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
            m <- sucWith ta_gr j el
            admissableM aut (n,m)
          _ <- forM [(n,el) | (n, el@(EdgeSymbol Data xt' Cns _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
            m <- sucWith ta_gr j el
            admissableM aut (m,n)
          return ()
        return ()
      subtypeCodata = do -- Maybe monad
        (Neg, HeadCons _ (Just codat1)) <- lab ta_gr i
        (Pos, HeadCons _ (Just codat2)) <- lab ta_gr j
        _ <- forM (S.toList codat2) $ \xt -> guard (xt `S.member` codat1)
        _ <- forM (S.toList codat2) $ \xt -> do
          _ <- forM [(n,el) | (n, el@(EdgeSymbol Data xt' Prd _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
            m <- sucWith ta_gr j el
            admissableM aut (m,n)
          _ <- forM [(n,el) | (n, el@(EdgeSymbol Data xt' Cns _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
            m <- sucWith ta_gr j el
            admissableM aut (n,m)
          return ()
        return ()
    in
      guard (e `elem` ta_flowEdges) <|> subtypeData <|> subtypeCodata


removeAdmissableFlowEdges :: TypeAutDet -> TypeAutDet
removeAdmissableFlowEdges aut@TypeAut{..} = aut { ta_flowEdges = filter (not . admissable aut) ta_flowEdges }

-------------------------------------------------------------------------------------
-- Flow analysis
-------------------------------------------------------------------------------------

type FlowGraph = Gr () ()

genFlowGraph :: TypeAut' EdgeLabel f -> FlowGraph
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

getFlowAnalysisMap :: TypeAut' EdgeLabel f -> Map Node (Set TVar)
getFlowAnalysisMap aut = fst $ runState (flowAnalysisState (genFlowGraph aut)) 0
