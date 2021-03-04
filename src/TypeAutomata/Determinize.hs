module TypeAutomata.Determinize
  ( determinize
  , removeEpsilonEdges
  , removeIslands
  ) where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS
import Data.Graph.Inductive.PatriciaTree

import Data.Functor.Identity
import Data.Maybe (catMaybes)
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Data.List.NonEmpty (NonEmpty(..))
import Control.Monad.State
import Data.Void
import Syntax.CommonTerm
import Syntax.Types
import Syntax.TypeGraph
import Utils

---------------------------------------------------------------------------------------
-- Generic epsilon edge removal algorithm
---------------------------------------------------------------------------------------

delAllLEdges :: Eq b => [LEdge b] -> Gr NodeLabel b -> Gr NodeLabel b
delAllLEdges es gr = foldr delAllLEdge gr es

removeEpsilonEdges' :: Node -> (TypeGrEps, [Node]) -> (TypeGrEps, [Node])
removeEpsilonEdges' n (gr,starts) =
  ( delAllLEdges [(n,j, EpsilonEdge ()) | (j, EpsilonEdge _) <- lsuc gr n]
  . insEdges [(i,j,el) | (j, EpsilonEdge _) <- lsuc gr n, (i,el) <- lpre gr n]
  $ gr
  , if n `elem` starts
      then starts ++ [j | (j,EpsilonEdge _) <- lsuc gr n]
      else starts)

fromEpsGr :: TypeGrEps -> TypeGr
fromEpsGr gr = gmap mapfun gr
  where
    foo :: Adj EdgeLabelEpsilon -> Adj EdgeLabelNormal
    foo = fmap (\(el, node) -> (unsafeEmbedEdgeLabel el, node))
    mapfun :: Context NodeLabel EdgeLabelEpsilon -> Context NodeLabel EdgeLabelNormal
    mapfun (ins,i,nl,outs) = (foo ins, i, nl, foo outs)

removeRedundantEdges :: TypeGr -> TypeGr
removeRedundantEdges = gmap (\(ins,i,l,outs) -> (nub ins, i, l, nub outs))

removeEpsilonEdges :: TypeAutEps pol -> TypeAut pol
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

removeIslands :: TypeAut pol -> TypeAut pol
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

getAlphabetForNodes :: Ord b => Gr NodeLabel b -> Set Node -> [b]
getAlphabetForNodes gr ns = nub $ map (\(_,_,b) -> b) (concat (map (out gr) (S.toList ns)))

succsWith :: Eq b => Gr NodeLabel b -> Set Node -> b -> Set Node
succsWith gr ns x = S.fromList $ map fst . filter ((==x).snd) . concat $ map (lsuc gr) (S.toList ns)

determinizeState :: Ord b => [Set Node] -> Gr NodeLabel b -> State (Map (Set Node) [((Set Node),b)]) ()
determinizeState [] _ = return ()
determinizeState (ns:rest) gr = do
  mp <- get
  if ns `elem` M.keys mp then determinizeState rest gr
    else do
      let newEdges = map (\x -> (succsWith gr ns x, x)) (getAlphabetForNodes gr ns)
      let newNodeSets = map fst newEdges
      modify (M.insert ns newEdges)
      determinizeState (newNodeSets ++ rest) gr

runDeterminize :: Ord b => Gr NodeLabel b -> [Node] -> Map (Set Node) [((Set Node),b)]
runDeterminize gr starts = snd $ runState (determinizeState [S.fromList starts] gr) M.empty

getNewNodeLabel :: ([NodeLabel] -> NodeLabel) -> Gr NodeLabel b -> Set Node -> NodeLabel
getNewNodeLabel f gr ns = f $ catMaybes (map (lab gr) (S.toList ns))

-- first argument is the node label "combiner"
-- second result argument is a mapping from sets of node ids to new node ids
-- this is necessary to correctly handle flow edges, which is done later
determinize' :: Ord b => ([NodeLabel] -> NodeLabel) -> (Gr NodeLabel b, [Node]) -> (Gr NodeLabel b, Node, [(Node, (Set Node))])
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
  = if not . allEq $ (map hc_pol nls)
      then error "Tried to combine node labels of different polarity!"
      else HeadCons {
        hc_pol = pol,
        hc_data = mrgDat [xtors | HeadCons _ (Just xtors) _ _ <- nls],
        hc_codata = mrgCodat [xtors | HeadCons _ _ (Just xtors) _ <- nls],
        hc_nominal = S.unions [ tn | HeadCons _ _ _ tn <- nls]
        }
  where
    pol = hc_pol (head nls)
    mrgDat [] = Nothing
    mrgDat (xtor:xtors) = Just $ case pol of {Pos -> S.unions (xtor:xtors) ; Neg -> intersections (xtor :| xtors) }
    mrgCodat [] = Nothing
    mrgCodat (xtor:xtors) = Just $ case pol of {Pos -> intersections (xtor :| xtors); Neg -> S.unions (xtor:xtors)}

determinize :: TypeAut pol -> TypeAutDet pol
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

containsXtor :: DataCodata -> NodeLabel -> XtorName -> Bool
containsXtor Data (HeadCons _ Nothing _ _) _ = False
containsXtor Codata (HeadCons _ _ Nothing _) _ = False
containsXtor Data (HeadCons _ (Just xtors) _ _) xt = xt `S.member` xtors
containsXtor Codata (HeadCons _ _ (Just xtors) _) xt = xt `S.member` xtors

isFaultyEdge :: TypeGr -> LEdge EdgeLabelNormal -> Bool
isFaultyEdge gr (i,_,EdgeSymbol s xt _ _) = not $ containsXtor s (fromJust (lab gr i)) xt
isFaultyEdge _ (_,_,EpsilonEdge v) = absurd v

removeFaultyEdges :: TypeGr -> TypeGr
removeFaultyEdges gr = delAllLEdges (filter (isFaultyEdge gr) (labEdges gr)) gr
