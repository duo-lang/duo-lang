module TypeAutomata.Determinize
  ( determinize
  , removeEpsilonEdges
  , removeIslands
  ) where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS

import Data.Functor.Identity
import Data.Maybe (catMaybes)
import Data.Bifunctor
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import Control.Monad.State
import Syntax.Terms
import Syntax.Types
import Syntax.TypeGraph
import Utils

---------------------------------------------------------------------------------------
-- Generic epsilon edge removal algorithm
---------------------------------------------------------------------------------------

delAllLEdges :: (DynGraph gr, Eq b) => [LEdge b] -> gr a b -> gr a b
delAllLEdges es gr = foldr delAllLEdge gr es

removeEpsilonEdges' :: (DynGraph gr, Eq b) => Node -> (gr a (Maybe b), [Node]) -> (gr a (Maybe b), [Node])
removeEpsilonEdges' n (gr,starts) =
  ( delAllLEdges [(n,j,Nothing) | (j,Nothing) <- lsuc gr n]
  . insEdges [(i,j,el) | (j,Nothing) <- lsuc gr n, (i,el) <- lpre gr n]
  $ gr
  , if n `elem` starts
      then starts ++ [j | (j,Nothing) <- lsuc gr n]
      else starts)

fromEpsGr :: DynGraph gr => gr a (Maybe b) -> gr a b
fromEpsGr gr = gmap (\(ins,i,nl,outs) -> (map (bimap fromJust id) ins, i, nl, map (bimap fromJust id) outs)) gr

removeRedundantEdges :: (DynGraph gr, Eq a, Ord b) => gr a b -> gr a b
removeRedundantEdges = gmap (\(ins,i,l,outs) -> (nub ins, i, l, nub outs))

removeEpsilonEdges :: TypeAutEps -> TypeAut
removeEpsilonEdges TypeAut { ta_gr, ta_starts, ta_flowEdges } =
  let
    (gr', starts') = foldr (.) id (map removeEpsilonEdges' (nodes ta_gr)) (ta_gr, ta_starts)
  in
   TypeAut { ta_gr = (removeRedundantEdges . fromEpsGr) gr'
           , ta_starts = starts'
           , ta_flowEdges = ta_flowEdges
           }

---------------------------------------------------------------------------------------
-- Remove islands not reachable from starting states.
---------------------------------------------------------------------------------------

removeIslands :: TypeAut -> TypeAut
removeIslands TypeAut{..} =
  let
    reachableNodes = dfs ta_starts ta_gr
    reachableFlowEdges = [(i,j) | (i,j) <- ta_flowEdges, i `elem` reachableNodes, j `elem` reachableNodes]
  in
    TypeAut { ta_gr = subgraph reachableNodes ta_gr
            , ta_starts = ta_starts
            , ta_flowEdges = reachableFlowEdges
            }

---------------------------------------------------------------------------------------
-- Generic determinization algorithm
---------------------------------------------------------------------------------------

getAlphabetForNodes :: (DynGraph gr, Ord b) => gr a b -> Set Node -> [b]
getAlphabetForNodes gr ns = nub $ map (\(_,_,b) -> b) (concat (map (out gr) (S.toList ns)))

succsWith :: (DynGraph gr, Eq b) => gr a b -> Set Node -> b -> Set Node
succsWith gr ns x = S.fromList $ map fst . filter ((==x).snd) . concat $ map (lsuc gr) (S.toList ns)

determinizeState :: (DynGraph gr, Ord b) => [Set Node] -> gr a b -> State (Map (Set Node) [((Set Node),b)]) ()
determinizeState [] _ = return ()
determinizeState (ns:rest) gr = do
  mp <- get
  if ns `elem` M.keys mp then determinizeState rest gr
    else do
      let newEdges = map (\x -> (succsWith gr ns x, x)) (getAlphabetForNodes gr ns)
      let newNodeSets = map fst newEdges
      modify (M.insert ns newEdges)
      determinizeState (newNodeSets ++ rest) gr

runDeterminize :: (DynGraph gr, Ord b) => gr a b -> [Node] -> Map (Set Node) [((Set Node),b)]
runDeterminize gr starts = snd $ runState (determinizeState [S.fromList starts] gr) M.empty

getNewNodeLabel :: (DynGraph gr) => ([a] -> c) -> gr a b -> Set Node -> c
getNewNodeLabel f gr ns = f $ catMaybes (map (lab gr) (S.toList ns))

-- first argument is the node label "combiner"
-- second result argument is a mapping from sets of node ids to new node ids
-- this is necessary to correctly handle flow edges, which is done later
determinize' :: (DynGraph gr, Ord b) => ([a] -> c) -> (gr a b, [Node]) -> (gr c b, Node, [(Node, (Set Node))])
determinize' f (gr,starts) =
  let
    mp = runDeterminize gr starts
  in ( mkGraph [(i, getNewNodeLabel f gr ns) | (ns,_) <- M.toList mp, let i = M.findIndex ns mp]
               [(i, M.findIndex ns' mp,el) | (ns,es) <- M.toList mp, let i = M.findIndex ns mp, (ns',el) <- es]
     , M.findIndex (S.fromList starts) mp
     , [(M.findIndex nodeSet mp, nodeSet) | (nodeSet,_) <- M.toList mp])

------------------------------------------------------------------------------
-- Applied to type graphs
------------------------------------------------------------------------------

combineNodeLabels :: [NodeLabel] -> NodeLabel
combineNodeLabels nls
  = if not . allEq $ (map fst nls)
      then error "Tried to combine node labels of different polarity!"
      else (pol, HeadCons {
        hc_data = mrgDat [xtors | HeadCons (Just xtors) _ _ <- hcs],
        hc_codata = mrgCodat [xtors | HeadCons _ (Just xtors) _ <- hcs],
        hc_nominal = S.unions [ tn | HeadCons _ _ tn <- hcs]
        })
  where
    pol = fst (head nls)
    hcs = map snd nls
    mrgDat [] = Nothing
    mrgDat xtors = Just $ (case pol of {Prd -> S.unions; Cns -> intersections}) xtors
    mrgCodat [] = Nothing
    mrgCodat xtors = Just $ (case pol of {Prd -> intersections; Cns -> S.unions}) xtors

determinize :: TypeAut -> TypeAutDet
determinize TypeAut{..} =
  let
    (newgr, newstart, mp) = determinize' combineNodeLabels (ta_gr, ta_starts)
    newFlowEdges = [(i,j) | (i,ns) <- mp, (j,ms) <- mp,
                            not $ null [(n,m) | n <- S.toList ns, m <- S.toList ms, (n,m) `elem` ta_flowEdges]]
  in
    TypeAut { ta_gr = removeFaultyEdges newgr
            , ta_starts = Identity newstart
            , ta_flowEdges = newFlowEdges
            }

-------------------------------------------------------------------------
-- Removal of faulty edges
-------------------------------------------------------------------------

containsXtor :: DataCodata -> HeadCons -> XtorName -> Bool
containsXtor Data (HeadCons Nothing _ _) _ = False
containsXtor Codata (HeadCons _ Nothing _) _ = False
containsXtor Data (HeadCons (Just xtors) _ _) xt = xt `S.member` xtors
containsXtor Codata (HeadCons _ (Just xtors) _) xt = xt `S.member` xtors

isFaultyEdge :: TypeGr -> LEdge EdgeLabel -> Bool
isFaultyEdge gr (i,_,EdgeSymbol s xt _ _) = not $ containsXtor s (snd (fromJust (lab gr i))) xt

removeFaultyEdges :: TypeGr -> TypeGr
removeFaultyEdges gr = delAllLEdges (filter (isFaultyEdge gr) (labEdges gr)) gr
