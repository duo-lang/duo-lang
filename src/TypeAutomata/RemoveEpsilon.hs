module TypeAutomata.RemoveEpsilon ( removeEpsilonEdges ) where

import Data.Graph.Inductive.Graph
import Data.Bifunctor ( Bifunctor(first) )

import TypeAutomata.Definition

---------------------------------------------------------------------------------------
-- Generic epsilon edge removal algorithm
---------------------------------------------------------------------------------------

unsafeEmbedEdgeLabel :: EdgeLabelEpsilon -> EdgeLabelNormal
unsafeEmbedEdgeLabel (EdgeSymbol dc xt pc i) = EdgeSymbol dc xt pc i
unsafeEmbedEdgeLabel (EpsilonEdge _) = error "unsafeEmbedEdgeLabel failed"
unsafeEmbedEdgeLabel (RefineEdge tn) = RefineEdge tn
unsafeEmbedEdgeLabel (TypeArgEdge tn v i) = TypeArgEdge tn v i

-- | Remove all epsilon edges starting from the node n.
-- I.e. replace this configuration:
--
--    ----------             -----                --------
--    |  pred  | ---edge---> | n | ---epsilon---> | succ |
--    ----------             -----                --------
--
-- by this configuration:
--
--    ----------             -----
--    |  pred  | ---edge---> | n |
--    ----------             -----
--        |
--       edge
--        |
--        \/
--     ---------
--     | succ  |
--     ---------
--
-- If n is a starting state, we have to turn all of its epsilon
-- successors also into starting states.
removeEpsilonEdgesFromNode :: Node -> (TypeGrEps, [Node]) -> (TypeGrEps, [Node])
removeEpsilonEdgesFromNode n (gr,starts) = (newGraph, newStarts)
  where
    -- | All epsilon edges starting from n (going to succ).
    outgoingEps = [(n,succ, EpsilonEdge ()) | (succ, EpsilonEdge _) <- lsuc gr n]
    -- | The new edges going from the predecessors of n to its epsilon successors.
    newEdges = [(pred,succ,edge) | (succ, EpsilonEdge _) <- lsuc gr n, (pred,edge) <- lpre gr n]
    newGraph = (delAllLEdges outgoingEps  . insEdges newEdges) gr
    newStarts = if n `elem` starts
                then starts ++ [j | (j,EpsilonEdge _) <- lsuc gr n]
                else starts

fromEpsGr :: TypeGrEps -> TypeGr
fromEpsGr = gmap mapfun
  where
    foo :: Adj EdgeLabelEpsilon -> Adj EdgeLabelNormal
    foo = fmap (first unsafeEmbedEdgeLabel)
    mapfun :: Context NodeLabel EdgeLabelEpsilon -> Context NodeLabel EdgeLabelNormal
    mapfun (ins,i,nl,outs) = (foo ins, i, nl, foo outs)

removeEpsilonEdges :: TypeAutEps pol -> TypeAut pol
removeEpsilonEdges TypeAut { ta_pol, ta_starts, ta_core = TypeAutCore { ta_flowEdges, ta_gr } } =
  let
    (gr', starts') = foldr ((.) . removeEpsilonEdgesFromNode) id (nodes ta_gr) (ta_gr, ta_starts)
  in
   TypeAut { ta_pol = ta_pol
           , ta_starts = starts'
           , ta_core = TypeAutCore
             { ta_gr = (removeRedundantEdges . fromEpsGr) gr'
             , ta_flowEdges = ta_flowEdges
             }
           }
