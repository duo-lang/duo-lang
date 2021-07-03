module TypeAutomata.Determinize ( determinize ) where

import Control.Monad.State
import Data.Functor.Identity
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (mapMaybe)
import Data.Set (Set)
import qualified Data.Set as S

import Syntax.Types
import TypeAutomata.Definition
import Utils

---------------------------------------------------------------------------------------
-- Generic determinization algorithm
---------------------------------------------------------------------------------------

getAlphabetForNodes :: Ord b => Gr NodeLabel b -> Set Node -> [b]
getAlphabetForNodes gr ns = nub $ map (\(_,_,b) -> b) (concatMap (out gr) (S.toList ns))

succsWith :: Eq b => Gr NodeLabel b -> Set Node -> b -> Set Node
succsWith gr ns x = S.fromList $ map fst . filter ((==x).snd) $ concatMap (lsuc gr) (S.toList ns)

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
runDeterminize gr starts = execState (determinizeState [S.fromList starts] gr) M.empty

getNewNodeLabel :: ([NodeLabel] -> NodeLabel) -> Gr NodeLabel b -> Set Node -> NodeLabel
getNewNodeLabel f gr ns = f $ mapMaybe (lab gr) (S.toList ns)

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
  = if not . allEq $ (map nl_pol nls)
      then error "Tried to combine node labels of different polarity!"
      else MkNodeLabel {
        nl_pol = pol,
        nl_data = mrgDat [xtors | MkNodeLabel _ (Just xtors) _ _ _ <- nls],
        nl_codata = mrgCodat [xtors | MkNodeLabel _ _ (Just xtors) _ _ <- nls],
        nl_nominal = S.unions [ tn | MkNodeLabel _ _ _ tn _ <- nls],
        nl_refined = S.unions [ tr | MkNodeLabel _ _ _ _ tr <- nls]
        }
  where
    pol = nl_pol (head nls)
    mrgDat [] = Nothing
    mrgDat (xtor:xtors) = Just $ case pol of {Pos -> S.unions (xtor:xtors) ; Neg -> intersections (xtor :| xtors) }
    mrgCodat [] = Nothing
    mrgCodat (xtor:xtors) = Just $ case pol of {Pos -> intersections (xtor :| xtors); Neg -> S.unions (xtor:xtors)}

-- | Checks for all nodes if there are multiple refinement nodes refining the same type. If so, the multiple
-- refining nodes are combined into one.
mergeRefinements :: Gr NodeLabel EdgeLabelNormal -> State (Gr NodeLabel EdgeLabelNormal) ()
mergeRefinements oldGr = do
  forM_ (labNodes oldGr) (\(node,MkNodeLabel{ nl_refined }) ->
      case S.toList nl_refined of { [] -> return (); tyNames -> do
          gr <- get
          let (_,_,_,outs) = context gr node
          forM_ tyNames (\tn -> do
            let refs = concatMap (\(label,node) -> case label of { RefineEdge tn' | tn'==tn -> [node]; _ -> [] }) outs
            let newLabel = combineNodeLabels $ mapMaybe (lab gr) refs
            modify $ delNodes refs
            gr <- get
            let [newNode] = newNodes 1 gr
            modify $ insNode (newNode, newLabel)
            modify $ insEdge (node,newNode,RefineEdge tn)
            return () )})

determinize :: TypeAut pol -> TypeAutDet pol
determinize TypeAut{ ta_pol, ta_starts, ta_core = TypeAutCore { ta_gr, ta_flowEdges }} =
  let
    (newgr, newstart, mp) = determinize' combineNodeLabels (ta_gr, ta_starts)
    newFlowEdges = [(i,j) | (i,ns) <- mp, (j,ms) <- mp,
                            not $ null [(n,m) | n <- S.toList ns, m <- S.toList ms, (n,m) `elem` ta_flowEdges]]
    newgr' = execState (mergeRefinements newgr) newgr
  in
    TypeAut { ta_pol = ta_pol
            , ta_starts = Identity newstart
            , ta_core = TypeAutCore
              { ta_gr = newgr'
              , ta_flowEdges = newFlowEdges
              }
            }

