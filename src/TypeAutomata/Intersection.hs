module TypeAutomata.Intersection (emptyIntersection,intersectIsEmpty,intersectAut) where


import TypeAutomata.Definition (TypeAutDet, TypeAut' (..), TypeAutCore (..), NodeLabel (..), EdgeLabelNormal, TypeAut)
import Control.Monad.Identity (Identity(..))
import Data.Graph.Inductive.Graph (Node, Graph (..), lsuc, lab)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe, isJust)
import Control.Monad.State
import qualified Data.Bifunctor as BF
import Data.List (nub, (\\))

import Syntax.TST.Types (TypeScheme(..))
import Data.List.NonEmpty (NonEmpty)
import Errors
import TypeAutomata.Minimize (minimize)
import TypeAutomata.RemoveAdmissible (removeAdmissableFlowEdges)
import TypeAutomata.Determinize (determinize)
import TypeAutomata.RemoveEpsilon (removeEpsilonEdges)
import TypeAutomata.ToAutomaton (typeToAut)
import Data.Map (Map)
import TypeAutomata.Utils (typeAutIsEmpty, isEmptyLabel)
import TypeAutomata.Simplify (printGraph)
import Pretty.Pretty (ppPrint)
import qualified Data.Text as T


-- | Check for two type schemes whether their intersection type automaton is empty.
emptyIntersection :: TypeScheme pol -> TypeScheme pol -> Either (NonEmpty Error) Bool
emptyIntersection ty1 ty2 = do
  aut1 <- minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges <$> typeToAut ty1
  aut2 <- minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges <$> typeToAut ty2
  checkEmptyIntersection aut1 aut2


checkEmptyIntersection :: TypeAutDet pol -> TypeAutDet pol -> Either (NonEmpty Error) Bool
checkEmptyIntersection (TypeAut _ (Identity starts1) (TypeAutCore gr1 _flowEdges1))
                       (TypeAut _ (Identity starts2) (TypeAutCore gr2 _flowEdges2))
  = evalStateT (explore gr1 gr2) (ExploreState { known = [], todos = [(starts1, starts2)] })


data ExploreState
  = ExploreState
  { known :: [(Node, Node)]
  , todos :: [(Node, Node)]
  }

type ExploreM = StateT ExploreState (Either (NonEmpty Error))

-- | Exhaustively explore the intersection of two graphs and return true if it is empty.
explore :: Graph gr => gr NodeLabel EdgeLabelNormal
                    -> gr NodeLabel EdgeLabelNormal
                    -> ExploreM Bool
explore gr1 gr2 = do
  todos <- gets todos
  case todos of
    [] -> pure True
    (n,m):rest -> do
      -- get reachable nodes
      let nexts = lsuc gr1 n
      let nexts' = lsuc gr2 m
      -- check if edge labels match and get nodelabels
      let unsafeLab gr n = fromMaybe (error "successor node is not in graph") $ lab gr n
      let newNodes = [ (n, m) | (n, l) <- nexts, (m, l') <- nexts', l == l' ]
      -- check if node labels can be safely merged
      let merged = uncurry intersectLabels <$> (BF.bimap (unsafeLab gr1) (unsafeLab gr2) <$> newNodes)
      -- if label is non-empty, fail (non-empty intersection)
      if all isEmptyLabel (fromMaybe (error "intersectLabels returned Nothing") <$> merged)
        then do
          modify (\(ExploreState { known }) -> ExploreState { known = (n,m):known, todos = nub $ (newNodes \\ known) ++ rest })
          explore gr1 gr2
        else pure False

-- | Intersection of labels, returns Nothing if labels cannot be safely combined.
intersectLabels :: NodeLabel -> NodeLabel -> Maybe NodeLabel
intersectLabels (MkNodeLabel pol  data'  codata  nominal  ref_data  ref_codata  kind )
                (MkNodeLabel pol' data'' codata' nominal' ref_data' ref_codata' kind')
 | pol /= pol' = Nothing
 | kind /= kind' = Nothing
 | otherwise = Just $ MkNodeLabel pol (S.intersection <$> data' <*> data'')
                                      (S.intersection <$> codata <*> codata')
                                      (S.intersection nominal nominal')
                                      (M.intersectionWith S.intersection ref_data ref_data')
                                      (M.intersectionWith S.intersection ref_codata ref_codata') kind
intersectLabels (MkPrimitiveNodeLabel pol prim)
                (MkPrimitiveNodeLabel pol' prim')
 | pol /= pol' = Nothing
 | prim /= prim' = Nothing
 | otherwise = Just $ MkPrimitiveNodeLabel pol prim
intersectLabels _ _ = Nothing

-- | Check for two type schemes whether their intersection type automaton is empty.
intersectIsEmpty :: MonadIO m => Bool -> TypeScheme pol -> TypeScheme pol -> m Bool
intersectIsEmpty print ty1 ty2 = do
  case (tyToMinAut ty1, tyToMinAut ty2) of
    (Right aut1, Right aut2) -> do
      let intersect = intersectAut aut1 aut2
      printGraph print False ("inter" <> T.unpack (ppPrint ty1) <> "x" <> T.unpack (ppPrint ty2)) intersect
      pure $ typeAutIsEmpty intersect
    _ -> pure False
  where
    tyToMinAut :: TypeScheme pol -> Either (NonEmpty Error) (TypeAutDet pol)
    tyToMinAut ty = minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges <$> typeToAut ty

-- | Create  the intersection automaton of two type automata.
intersectAut :: TypeAutDet pol -> TypeAutDet pol -> TypeAutDet pol
--  intersectAut aut1 aut2 = minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges $ intersectAutM aut1 aut2
intersectAut aut1 aut2 = minimize . removeAdmissableFlowEdges . determinize $ intersected
  where
    intersected = runIdentity $ flip evalStateT initState $ runIntersect $ intersectAutM aut1 aut2
    initState = IS { is_nodes = M.empty, is_nodelabels = M.empty, is_edges = M.empty, is_counter = 0, is_todo = [(runIdentity $ ta_starts aut1, runIdentity $ ta_starts aut2)] }

data IntersectS
  = IS { is_nodes :: Map (Node,Node) Node
       -- ^ map pairs of nodes from original automata to nodes in result automaton
       , is_nodelabels :: Map Node NodeLabel
       -- ^ labels of nodes in result automaton
       , is_edges :: Map Node [(Node, Node, EdgeLabelNormal)]
       -- ^ edges going from a result node to pairs of original nodes
       , is_counter :: Node
       -- ^ fresh node ID for result automaton
       , is_todo :: [(Node, Node)]
       -- ^ node pairs that still need to be visited
       }

newtype IntersectM' m a = IM { runIntersect :: StateT IntersectS m a }
  deriving newtype (Functor,Applicative,Monad,MonadState IntersectS)

type IntersectM = IntersectM' Identity

addNode :: (Node,Node) -> IntersectM Node
addNode (nl,nr) = do
  c <- gets is_counter
  modify (\is@IS { is_nodes } -> is { is_nodes = M.insert (nl,nr) c is_nodes, is_counter = c+1 })
  return c

intersectAutM :: TypeAutDet pol -> TypeAutDet pol -> IntersectM (TypeAut pol)
intersectAutM aut1 aut2 = do
    starts <- gets (head . is_todo)
    go
    nodes <- gets (M.toList . is_nodelabels)
    nodeM <- gets is_nodes
    edges' <- gets (M.toList . is_edges)
    let edges = concatMap (\(n,es) -> map (\(n1,n2,l) -> (n, nodeM M.! (n1,n2), l)) es) edges'
    let gr = mkGraph nodes edges
    start <- gets (flip (M.!) starts . is_nodes)
    -- TODO: get flow edges
    let fl = []
    pure $ TypeAut { ta_core = TypeAutCore { ta_gr = gr, ta_flowEdges = fl }, ta_starts = [start], ta_pol = ta_pol aut1 }
  where
    gr1 = ta_gr (ta_core aut1)
    gr2 = ta_gr (ta_core aut2)
    go :: IntersectM ()
    go = do
      todos <- gets is_todo
      cache <- gets is_nodes
      case todos of
        [] -> pure ()
        (todo@(n1,n2):todos') -> flip (>>) go $ if isJust $ todo `M.lookup` cache
          then modify (\is -> is { is_todo = todos' }) 
          else do
            let unsafeLab gr n = fromMaybe (error "successor node is not in graph") $ lab gr n
            let l1 = unsafeLab gr1 n1
            let l2 = unsafeLab gr2 n2
            let lIntersect = fromMaybe (error $ "could not intersect labels in " ++ show l1 ++ " " ++ show l2) $ intersectLabels l1 l2
            n <- addNode (n1,n2)
            modify (\is@IS { is_nodelabels = labs } -> is { is_nodelabels = M.insert n lIntersect labs })
            let nexts1 = lsuc gr1 n1
            let nexts2 = lsuc gr2 n2
            let outEdges = [ (n1, n2, l) | (n1, l) <- nexts1, (n2, l') <- nexts2, l == l' ]
            modify $ \is@IS { is_edges = edges } -> is { is_edges = M.insert n outEdges edges
                                                       , is_todo  = ((\(n,m,_) -> (n,m)) <$> outEdges) ++ todos'
                                                       }
            go

            
          


