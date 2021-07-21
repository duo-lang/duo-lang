module TypeAutomata.Determinize ( determinize ) where

import Control.Monad.State
import Data.Functor.Identity
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Syntax.Types
import TypeAutomata.Definition
import Utils
import Data.Maybe (mapMaybe)

---------------------------------------------------------------------------------------
-- First step of determinization:
-- Compute the new transition function for the determinized graph,
-- using the powerset construction.
---------------------------------------------------------------------------------------

-- | A transition function for the powerset construction
type TransFun = Map (Set Node) [(Set Node, EdgeLabelNormal)]

-- | Collect all (unique) outgoing edgelabels from the given set of nodes.
getAlphabetForNodes :: Gr NodeLabel EdgeLabelNormal -> Set Node -> [EdgeLabelNormal]
getAlphabetForNodes gr ns = nub $ map (\(_,_,b) -> b) (concatMap (out gr) (S.toList ns))

-- | Get all successor nodes from the given set which are connected by the given edgeLabel.
succsWith :: Gr NodeLabel EdgeLabelNormal -> Set Node -> EdgeLabelNormal -> Set Node
succsWith gr ns x = S.fromList $ map fst . filter ((==x).snd) $ concatMap (lsuc gr) (S.toList ns)

determinizeState :: [Set Node]
                 -> Gr NodeLabel EdgeLabelNormal
                 -> State TransFun ()
determinizeState [] _ = pure ()
determinizeState (ns:rest) gr = do
  mp <- get
  if ns `elem` M.keys mp then determinizeState rest gr
    else do
      let alphabet = getAlphabetForNodes gr ns
      let newEdges = map (\x -> (succsWith gr ns x, x)) alphabet
      modify (M.insert ns newEdges)
      let newNodeSets = map fst newEdges
      determinizeState (newNodeSets ++ rest) gr

-- | Compute the transition function for the powerset construction.
computeTransFun :: Gr NodeLabel EdgeLabelNormal
               -> Set Node -- ^ Starting states
               -> TransFun
computeTransFun gr starts = execState (determinizeState [starts] gr) M.empty

---------------------------------------------------------------------------------------
-- Compute a new type graph from the TransFun and the old type graph.
---------------------------------------------------------------------------------------

-- | Return the combined node label for the given set of nodes.
getNewNodeLabel :: Gr NodeLabel b -> Set Node -> NodeLabel
getNewNodeLabel gr ns = combineNodeLabels $ mapMaybe (lab gr) (S.toList ns)

combineNodeLabels :: [NodeLabel] -> NodeLabel
combineNodeLabels nls
  = if not . allEq $ map nl_pol nls
      then error "Tried to combine node labels of different polarity!"
      else MkNodeLabel {
        nl_pol = pol,
        nl_data = mrgDat [xtors | MkNodeLabel _ (Just xtors) _ _ <- nls],
        nl_codata = mrgCodat [xtors | MkNodeLabel _ _ (Just xtors) _ <- nls],
        nl_nominal = S.unions [ tn | MkNodeLabel _ _ _ tn <- nls]
        }
  where
    pol = nl_pol (head nls)
    mrgDat [] = Nothing
    mrgDat (xtor:xtors) = Just $ case pol of {Pos -> S.unions (xtor:xtors) ; Neg -> intersections (xtor :| xtors) }
    mrgCodat [] = Nothing
    mrgCodat (xtor:xtors) = Just $ case pol of {Pos -> intersections (xtor :| xtors); Neg -> S.unions (xtor:xtors)}

-- | This function computes the new typegraph and the new starting state.
-- The nodes for the new typegraph are computed as the indizes of the sets of nodes in the TransFun map.
computeNewTypeGraph :: TransFun -- ^ The transition function of the powerset construction.
             -> (Gr NodeLabel EdgeLabelNormal, Set Node) -- ^ The old typegraph with a set of starting states.
             -> (Gr NodeLabel EdgeLabelNormal, Node) -- ^ The new typegraph with one starting state.
computeNewTypeGraph transFun (gr, starts) =
  let
    nodes = [(i, getNewNodeLabel gr ns) | (ns,_) <- M.toList transFun, let i = M.findIndex ns transFun]
    edges = [(i, M.findIndex ns' transFun,el) | (ns,es) <- M.toList transFun, let i = M.findIndex ns transFun, (ns',el) <- es]
  in (mkGraph nodes edges, M.findIndex starts transFun)

------------------------------------------------------------------------------
-- Compute new flowEdges
------------------------------------------------------------------------------

-- | Compute the flow edges for the new automaton.
-- In the new automaton, a flow edge exists between two nodes if a flow edge existed between any one of the elements of the powersets.
computeFlowEdges :: TransFun
                 -> [(Node,Node)] -- ^ Old flowedges
                 -> [(Node,Node)] -- ^ New flowedges
computeFlowEdges mp' flowedges =
  let
    mp = [(M.findIndex nodeSet mp', nodeSet) | (nodeSet,_) <- M.toList mp']
  in
    [(i,j) | (i,ns) <- mp, (j,ms) <- mp, not $ null [(n,m) | n <- S.toList ns, m <- S.toList ms, (n,m) `elem` flowedges]]

------------------------------------------------------------------------------
-- Lift the determinization algorithm to type graphs.
------------------------------------------------------------------------------

determinize :: TypeAut pol -> TypeAutDet pol
determinize TypeAut{ ta_pol, ta_starts, ta_core = TypeAutCore { ta_gr, ta_flowEdges }} =
  let
    starts = S.fromList ta_starts
    transFun = computeTransFun ta_gr starts
    newFlowEdges = computeFlowEdges transFun ta_flowEdges
    (newgr, newstart) = computeNewTypeGraph transFun (ta_gr, starts)
    newCore = TypeAutCore { ta_gr = newgr, ta_flowEdges = newFlowEdges }
  in
    TypeAut { ta_pol = ta_pol, ta_starts = Identity newstart, ta_core = newCore }

