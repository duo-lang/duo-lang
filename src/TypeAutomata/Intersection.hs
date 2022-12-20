module TypeAutomata.Intersection (emptyIntersection, intersection) where


import TypeAutomata.Definition (TypeAutDet, TypeAut' (TypeAut), TypeAutCore (TypeAutCore), NodeLabel (..))
import Control.Monad.Identity (Identity(..))
import Control.Monad.State
import Data.Graph.Inductive.Graph (Node, Edge, LNode, LEdge, toEdge, Graph (..), mkUGraph)
import Data.Graph.Inductive.Query.DFS (dfs)
import Data.Set (Set)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Map (Map)
import Data.Maybe (fromMaybe)


emptyIntersection :: TypeAutDet pol -> TypeAutDet pol -> Bool
emptyIntersection (TypeAut _ (Identity s1) (TypeAutCore gr1 _flowEdges1))
                  (TypeAut _ (Identity s2) (TypeAutCore gr2 _flowEdges2))
  = let m = evalState (combineNodes (unLabelNode <$> labNodes gr1) (unLabelNode <$> labNodes gr2)) 0
        start = fromMaybe (error "start not found in intersection automaton") (M.lookup (s1,s2) m)
    in emptyIntersection' start (getLabeledNodes (labNodes gr1) (labNodes gr2)) m
                          (unsafeCombineEdges m (unLabelEdge <$>labEdges gr1) (unLabelEdge <$>labEdges gr2))

emptyIntersection' :: Node -> Set (Node, Node) -> Map (Node, Node) Node -> [Edge] -> Bool
emptyIntersection' start labeled m edges = let gr = mkUGraph (M.elems m) edges
                                               -- ^ missing implementation for unlabeled graph
                                               reachable = dfs [start] gr
                                           in not $ any (\x -> maybe False (`elem` reachable) (M.lookup x m)) labeled

unLabelNode :: LNode a -> Node
unLabelNode = fst

unLabelEdge :: LEdge a -> Edge
unLabelEdge = toEdge

nextNode :: State Node Node
nextNode = get >>= \n -> put (n+1) >> pure n

getLabeledNodes :: [LNode NodeLabel] -> [LNode NodeLabel] -> Set (Node, Node)
getLabeledNodes ns ms =
    let emptyLabel (MkNodeLabel {nl_data = Nothing, nl_codata = Nothing, nl_nominal, nl_ref_data, nl_ref_codata})
                     = S.null nl_nominal && M.null nl_ref_data && M.null nl_ref_codata
        emptyLabel _ = False
    in S.fromList [ (n,m) | (n, l) <- ns, not (emptyLabel l), (m, l') <- ms, not (emptyLabel l') ]

combineNodes :: [Node] -> [Node] -> State Node (Map (Node, Node) Node)
combineNodes ns ms = M.fromList . concat <$>
  forM ns (\n -> do
    forM ms $ \m -> do
      n' <- nextNode
      pure ((n,m), n'))

unsafeCombineEdges :: Map (Node, Node) Node -> [Edge] -> [Edge] -> [Edge]
unsafeCombineEdges m edges = concatMap (\(from, to) ->
  map (\(from', to') ->
    let err     = error "unexpected assumption failure in combineEdges"
        newFrom = fromMaybe err (M.lookup (from, from') m)
        newTo   = fromMaybe err (M.lookup (to, to') m)
     in (newFrom, newTo)) edges)

intersection :: [Node] -> [Edge] -> [Node] -> [Edge] -> ([Node], [Edge])
intersection nodes edges nodes' edges' = let m = evalState (combineNodes nodes nodes') 0
                                   in (M.elems m, unsafeCombineEdges m edges edges')
