module TypeAutomata.Determinize ( determinize ) where

import Control.Monad.State
    ( execState, State, MonadState(get), modify )
import Data.Functor.Identity ( Identity(Identity) )
import Data.Graph.Inductive.Graph
    ( Node, lab, lsuc, out, Graph(mkGraph) )
import Data.Graph.Inductive.PatriciaTree ( Gr )
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)
import Data.Set qualified as S

import Syntax.AST.Types ( Polarity(Neg, Pos) )
import TypeAutomata.Definition
    ( EdgeLabelNormal,
      NodeLabel(..),
      Nubable(nub),
      TypeAut,
      TypeAut'(TypeAut, ta_pol, ta_starts, ta_core),
      TypeAutCore(TypeAutCore, ta_gr, ta_flowEdges),
      TypeAutDet )
import Utils ( allEq, intersections )
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
transFun :: Gr NodeLabel EdgeLabelNormal
               -> Set Node -- ^ Starting states
               -> TransFun
transFun gr starts = execState (determinizeState [starts] gr) M.empty

type TransFunReindexed = [(Node, Set Node, [(Node, EdgeLabelNormal)])]

reIndexTransFun :: TransFun -> TransFunReindexed
reIndexTransFun transFun =
  let 
    mp = [(M.findIndex nodeSet transFun, nodeSet, es) | (nodeSet,es) <- M.toList transFun]
    mp' = fmap (\(i,ns,es) -> (i,ns, fmap (\(ns',el) -> (M.findIndex ns' transFun, el)) es)) mp
  in mp'

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
        nl_data = mrgDat [xtors | MkNodeLabel _ (Just xtors) _ _ _ _ <- nls],
        nl_codata = mrgCodat [xtors | MkNodeLabel _ _ (Just xtors) _ _ _ <- nls],
        nl_nominal = S.unions [ tn | MkNodeLabel _ _ _ tn _ _ <- nls],
        nl_ref_data = mrgRefDat [refs | MkNodeLabel _ _ _ _ refs _ <- nls],
        nl_ref_codata = mrgRefCodat [refs | MkNodeLabel _ _ _ _ _ refs <- nls]
        }
  where
    pol = nl_pol (head nls)
    mrgDat [] = Nothing
    mrgDat (xtor:xtors) = Just $ case pol of {Pos -> S.unions (xtor:xtors) ; Neg -> intersections (xtor :| xtors) }
    mrgCodat [] = Nothing
    mrgCodat (xtor:xtors) = Just $ case pol of {Pos -> intersections (xtor :| xtors); Neg -> S.unions (xtor:xtors)}
    mrgRefDat refs = case pol of 
      Pos -> M.unionsWith S.union refs
      Neg -> M.unionsWith S.intersection refs
    mrgRefCodat refs = case pol of
      Pos -> M.unionsWith S.intersection refs
      Neg -> M.unionsWith S.union refs

-- | This function computes the new typegraph and the new starting state.
-- The nodes for the new typegraph are computed as the indizes of the sets of nodes in the TransFun map.
newTypeGraph :: TransFunReindexed -- ^ The transition function of the powerset construction.
             -> Gr NodeLabel EdgeLabelNormal -- ^ The old typegraph with a set of starting states.
             -> Gr NodeLabel EdgeLabelNormal -- ^ The new typegraph with one starting state.
newTypeGraph transFun gr =
  let
    nodes = fmap (\(i,ns,_) -> (i, getNewNodeLabel gr ns)) transFun
    edges = [(i,j,el) | (i,_,es) <- transFun, (j,el) <- es]
  in mkGraph nodes edges

------------------------------------------------------------------------------
-- Compute new flowEdges
------------------------------------------------------------------------------

flowEdges :: TransFunReindexed
                 -> [(Node,Node)] -- ^ Old flowedges
                 -> [(Node,Node)] -- ^ New flowedges
flowEdges transFun flowedges =
  [(i,j) | (i,ns,_) <- transFun, (j,ms,_) <- transFun, not $ null [(n,m) | n <- S.toList ns, m <- S.toList ms, (n,m) `elem` flowedges]]

------------------------------------------------------------------------------
-- Lift the determinization algorithm to type graphs.
------------------------------------------------------------------------------

determinize :: TypeAut pol -> TypeAutDet pol
determinize TypeAut{ ta_pol, ta_starts, ta_core = TypeAutCore { ta_gr, ta_flowEdges }} =
  let
    starts = S.fromList ta_starts
    newstart = M.findIndex starts newTransFun
    newTransFun = transFun ta_gr starts
    newTransFunReind = reIndexTransFun newTransFun
    newFlowEdges = flowEdges newTransFunReind ta_flowEdges
    newgr = newTypeGraph newTransFunReind ta_gr
    newCore = TypeAutCore { ta_gr = newgr, ta_flowEdges = newFlowEdges }
  in
    TypeAut { ta_pol = ta_pol, ta_starts = Identity newstart, ta_core = newCore }


