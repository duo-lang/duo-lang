module TypeAutomata.Intersection (emptyIntersection) where


import TypeAutomata.Definition (TypeAutDet, TypeAut' (..), TypeAutCore (..), NodeLabel (..), EdgeLabelNormal)
import Control.Monad.Identity (Identity(..))
import Data.Graph.Inductive.Graph (Node, Graph (..), lsuc, lab)
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe)
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


data ExploreState = ExploreState { known :: [(Node, Node)], todos :: [(Node, Node)] }
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

isEmptyLabel :: NodeLabel -> Bool
isEmptyLabel (MkNodeLabel {nl_data, nl_codata, nl_nominal, nl_ref_data, nl_ref_codata})
             = nothingOrEmpty nl_data && nothingOrEmpty nl_codata && S.null nl_nominal && M.null nl_ref_data && M.null nl_ref_codata
  where nothingOrEmpty Nothing = True
        nothingOrEmpty (Just s) = S.null s
isEmptyLabel _ = False

-- | Intersection of labels, returns Nothing if labels cannot be safely combined.
intersectLabels :: NodeLabel -> NodeLabel -> Maybe NodeLabel
intersectLabels (MkNodeLabel pol  data'  codata  nominal  ref_data  ref_codata  kind )
                (MkNodeLabel pol' data'' codata' nominal' ref_data' ref_codata' kind')
 | pol /= pol' = Nothing
 | kind /= kind' = Nothing
 | otherwise = Just $ MkNodeLabel pol (S.intersection <$> data' <*> data'')
                                      (S.intersection <$> codata <*> codata')
                                      (S.intersection nominal nominal')
                                      (M.intersection ref_data ref_data')
                                      (M.intersection ref_codata ref_codata') kind
intersectLabels (MkPrimitiveNodeLabel pol prim)
                (MkPrimitiveNodeLabel pol' prim')
 | pol /= pol' = Nothing
 | prim /= prim' = Nothing
 | otherwise = Just $ MkPrimitiveNodeLabel pol prim
intersectLabels _ _ = Nothing