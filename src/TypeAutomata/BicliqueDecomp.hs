module TypeAutomata.BicliqueDecomp
  ( FlowGraph
  , Biclique(..)
  , computeFlowMap
  ) where

import Data.Graph.Inductive.Graph
    ( delEdges, edges, neighbors, nodes, Node )
import Data.Graph.Inductive.PatriciaTree ( Gr )
import Data.List (intersect)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe ( mapMaybe )
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text qualified as T

import Syntax.CST.Names ( SkolemTVar(MkSkolemTVar) )

-------------------------------------------------------------------------------------
-- Compute Biclique Decomposition
-------------------------------------------------------------------------------------

type FlowGraph = Gr () ()

newtype Biclique = MkBiclique { unBiclique :: [Node] }

instance Eq Biclique where
    (MkBiclique bc1) == (MkBiclique bc2) = length bc1 == length bc2

instance Ord Biclique where
    compare (MkBiclique bc1) (MkBiclique bc2) = compare (length bc1) (length bc2)


-- Compute a biclique containing the given node.
computeBiclique :: FlowGraph -> Node -> Maybe Biclique
computeBiclique flgr i =
  let
    ns = neighbors flgr i
  in
    if null ns
      then Nothing
      else Just $ MkBiclique $  ns ++ foldr1 intersect (map (neighbors flgr) ns)

-- Delete all the edges of the given biclique from the FlowGraph.
deleteBiclique :: FlowGraph -> Biclique -> FlowGraph
deleteBiclique flgr (MkBiclique bc) = delEdges [(x,y) | (x,y) <- edges flgr, x `elem` bc, y `elem` bc] flgr

-- | Compute a Biclique decomposition of the Flowgraph by repeatedly removing the largest
-- Biclique from the Graph until none remain.
computeBicliqueDecomposition :: FlowGraph -> [Biclique]
computeBicliqueDecomposition flgr = go flgr []
  where
      go :: FlowGraph -> [Biclique] -> [Biclique]
      go flgr acc =
          let
              bicliques :: [Biclique] = mapMaybe (computeBiclique flgr) (nodes flgr)
          in
              case bicliques of
                  [] -> acc
                  bicliques@(_:_) ->
                      let
                          maximumBiclique :: Biclique = maximum bicliques
                          newGraph :: FlowGraph = deleteBiclique flgr maximumBiclique
                      in
                          go newGraph (maximumBiclique : acc)

-------------------------------------------------------------------------------------
-- Compute FlowMap
-------------------------------------------------------------------------------------

decompositionToFlowMap :: [Node] -> [Biclique] -> Map Node (Set SkolemTVar)
decompositionToFlowMap nodes bicliques = go bicliqueTvars (M.fromList [(n, S.empty ) | n <- nodes])
  where
      go :: [(Biclique, SkolemTVar)] -> Map Node (Set SkolemTVar) -> Map Node (Set SkolemTVar)
      go [] acc = acc
      go (x:xs) acc = go xs (insertBicliqueIntoMap x acc)

      bicliqueTvars :: [(Biclique, SkolemTVar)]
      bicliqueTvars = zip bicliques [MkSkolemTVar ("t" <> T.pack (show n)) | n <- [0 :: Int ..] ]

      insertBicliqueIntoMap :: (Biclique, SkolemTVar) -> Map Node (Set SkolemTVar) -> Map Node (Set SkolemTVar)
      insertBicliqueIntoMap (MkBiclique biclique, tv) m = foldr (M.adjust (S.insert tv)) m biclique



computeFlowMap :: FlowGraph -> Map Node (Set SkolemTVar)
computeFlowMap flgr = decompositionToFlowMap (nodes flgr) (computeBicliqueDecomposition flgr)
