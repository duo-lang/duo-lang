module TypeAutomata.Determinize ( determinize ) where

import Control.Monad.State
import Data.Functor.Identity
import Data.Graph.Inductive.Graph
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (catMaybes)
import Data.Set (Set)
import qualified Data.Set as S

import Syntax.Types
import TypeAutomata.Definition
import Utils

---------------------------------------------------------------------------------------
-- Generic determinization algorithm
---------------------------------------------------------------------------------------

combineNodeLabels :: [NodeLabel] -> NodeLabel
combineNodeLabels nls
  = if not . allEq $ (map nl_pol nls)
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

getAlphabetForNodes :: TypeGr -> Set Node -> [EdgeLabelNormal]
getAlphabetForNodes gr ns = nub $ map (\(_,_,b) -> b) (concat (map (out gr) (S.toList ns)))

succsWith :: TypeGr -> Set Node -> EdgeLabelNormal -> Set Node
succsWith gr ns x = S.fromList $ map fst . filter ((==x).snd) . concat $ map (lsuc gr) (S.toList ns)

determinizeState :: [Set Node] -> TypeGr -> State (Map (Set Node) [((Set Node),EdgeLabelNormal)]) ()
determinizeState [] _ = return ()
determinizeState (ns:rest) gr = do
  mp <- get
  if ns `elem` M.keys mp then determinizeState rest gr
    else do
      let newEdges = map (\x -> (succsWith gr ns x, x)) (getAlphabetForNodes gr ns)
      let newNodeSets = map fst newEdges
      modify (M.insert ns newEdges)
      determinizeState (newNodeSets ++ rest) gr

runDeterminize :: TypeGr -> [Node] -> Map (Set Node) [((Set Node),EdgeLabelNormal)]
runDeterminize gr starts = snd $ runState (determinizeState [S.fromList starts] gr) M.empty

getNewNodeLabel :: TypeGr -> Set Node -> NodeLabel
getNewNodeLabel gr ns = combineNodeLabels $ catMaybes (map (lab gr) (S.toList ns))

-- second result argument is a mapping from sets of node ids to new node ids
-- this is necessary to correctly handle flow edges, which is done later
determinize' :: (TypeGr, [Node]) -> (TypeGr, Node, [(Node, (Set Node))])
determinize' (gr,starts) = (gr', starts', fun)
  where
    mp = runDeterminize gr starts
    gr' = mkGraph [(i, getNewNodeLabel gr ns) | (ns,_) <- M.toList mp, let i = M.findIndex ns mp]
          [(i, M.findIndex ns' mp,el) | (ns,es) <- M.toList mp, let i = M.findIndex ns mp, (ns',el) <- es]
    starts' = M.findIndex (S.fromList starts) mp
    fun = [(M.findIndex nodeSet mp, nodeSet) | (nodeSet,_) <- M.toList mp]

------------------------------------------------------------------------------
-- Applied to type graphs
------------------------------------------------------------------------------

determinize :: TypeAut pol -> TypeAutDet pol
determinize TypeAut{ ta_pol, ta_starts, ta_core = TypeAutCore { ta_gr, ta_flowEdges }} =
  let
    (newgr, newstart, mp) = determinize' (ta_gr, ta_starts)
    newFlowEdges = [(i,j) | (i,ns) <- mp, (j,ms) <- mp,
                            not $ null [(n,m) | n <- S.toList ns, m <- S.toList ms, (n,m) `elem` ta_flowEdges]]
  in
    TypeAut { ta_pol = ta_pol
            , ta_starts = Identity newstart
            , ta_core = TypeAutCore
              { ta_gr = newgr
              , ta_flowEdges = newFlowEdges
              }
            }

