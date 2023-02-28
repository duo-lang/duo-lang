module TypeAutomata.Determinize ( determinize ) where

import Control.Monad.State
    ( execState, State, MonadState(get), modify )
import Data.Functor.Identity ( Identity(Identity) )
import Data.Graph.Inductive.Graph
    ( Node, lab, lsuc, out, Graph(mkGraph) )
import Data.Graph.Inductive.PatriciaTree ( Gr )
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.List qualified as L
import Data.Maybe (mapMaybe, fromMaybe)
import Data.Foldable (foldl')

import TypeAutomata.Definition
import Syntax.RST.Types ( Polarity(Neg, Pos) )
import Syntax.CST.Kinds (PolyKind(..))

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
succsWith gr ns x = S.fromList $ map fst . filter ((==x) . snd) $ concatMap (lsuc gr) (S.toList ns)

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
combineNodeLabels [] = error "No Labels to combine"
combineNodeLabels [fstLabel@MkNodeLabel{}] = fstLabel
combineNodeLabels (fstLabel@MkNodeLabel{}:rs) =
  case rs_merged of
    pr@MkPrimitiveNodeLabel{} -> error ("Tried to combine primitive type" <> show pr <> " and algebraic type " <> show fstLabel)
    combLabel@MkNodeLabel{} ->
      if combLabel.nl_kind.returnKind == knd.returnKind then 
        if combLabel.nl_pol  == pol then
          MkNodeLabel {
            nl_pol = pol,
            nl_data = mrgDat fstLabel.nl_data combLabel.nl_data, 
            nl_codata = mrgCodat fstLabel.nl_codata combLabel.nl_codata,
            nl_nominal = S.union fstLabel.nl_nominal combLabel.nl_nominal,
            nl_ref_data = mrgRefDat fstLabel.nl_ref_data combLabel.nl_ref_data, 
            nl_ref_codata = mrgRefCodat fstLabel.nl_ref_codata combLabel.nl_ref_codata, 
            nl_kind = MkPolyKind (mrgKindArgs combLabel.nl_kind.kindArgs knd.kindArgs) knd.returnKind
          }
        else
          error "Tried to combine node labels of different polarity!"
    else 
      error ("Tried to combine node labels of different kind" <> show combLabel.nl_kind <> " and " <> show knd)
  where
    pol = fstLabel.nl_pol
    knd = fstLabel.nl_kind

    mrgDat Nothing Nothing = Nothing
    mrgDat (Just xtors1) Nothing = Just xtors1
    mrgDat Nothing (Just xtors2) = Just xtors2
    mrgDat (Just xtors1) (Just xtors2) = Just $ case pol of {Pos -> S.union xtors1 xtors2; Neg -> S.intersection xtors1 xtors2}

    mrgCodat Nothing Nothing = Nothing
    mrgCodat (Just xtors1) Nothing = Just xtors1
    mrgCodat Nothing (Just xtors2) = Just xtors2
    mrgCodat (Just xtors1) (Just xtors2) = Just $ case pol of {Pos -> S.intersection xtors1 xtors2; Neg -> S.union xtors1 xtors2}

    mrgRefDat refs1 refs2 = 
      let mrgXtors xtors1 xtors2 = case pol of Pos -> S.union xtors1 xtors2; Neg -> S.intersection xtors1 xtors2
          f (xtors1, vars1) (xtors2, vars2) = (mrgXtors xtors1 xtors2, vars1 `L.union` vars2)
      in M.unionWith f refs1 refs2 
    mrgRefCodat refs1 refs2 = 
      let mrgXtors xtors1 xtors2 = case pol of Pos -> S.intersection xtors1 xtors2; Neg -> S.union xtors1 xtors2
          f (xtors1,vars1) (xtors2,vars2) = (mrgXtors xtors1 xtors2, vars1 `L.union` vars2)
      in M.unionWith f refs1 refs2
    rs_merged = combineNodeLabels rs
    mrgKindArgs [] knds = knds
    mrgKindArgs knds [] = knds
    mrgKindArgs (knd1:knds1) knds2 = if knd1 `elem` knds2 then mrgKindArgs knds1 knds2 else knd1:mrgKindArgs knds1 knds2
combineNodeLabels [fstLabel@MkPrimitiveNodeLabel{}] = fstLabel
combineNodeLabels (fstLabel@MkPrimitiveNodeLabel{}:rs) =
  case rs_merged of
    nl@MkNodeLabel{} -> error ("Tried to combine primitive type" <> show fstLabel <> " and algebraic type" <> show nl)
    combLabel@MkPrimitiveNodeLabel{} ->
      if combLabel.pl_pol == pol then
        if combLabel.pl_prim == primT then
          MkPrimitiveNodeLabel pol primT
        else
          error ("Tried to combine " <> primToStr primT <> " and " <> primToStr combLabel.pl_prim)
      else
        error "Tried to combine node labels of different polarity!"
  where
    pol = fstLabel.pl_pol
    primT = fstLabel.pl_prim
    rs_merged = combineNodeLabels rs
    primToStr typ = case typ of {I64 -> "I64"; F64 -> "F64" ; PChar -> "Char" ; PString -> "String"}

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
flowEdges transFun flowedges = nub $ concatMap reindexFlowEdge flowedges
  where
    getPartitions :: TransFunReindexed -> Map Node (Set Node) -> Map Node (Set Node)
    getPartitions tf m = foldl' (\m (n,ns,_) -> foldl' (\m n' -> M.insertWith S.union n' (S.singleton n) m) m ns) m tf

    partitionMap :: Map Node (Set Node)
    partitionMap = getPartitions transFun M.empty

    reindexFlowEdge :: (Node,Node) -> [(Node,Node)]
    reindexFlowEdge (l,r) = [ (l',r') | l' <- S.toList $ fromMaybe S.empty $ M.lookup l partitionMap,
                                        r' <- S.toList $ fromMaybe S.empty $ M.lookup r partitionMap]

------------------------------------------------------------------------------
-- Lift the determinization algorithm to type graphs.
------------------------------------------------------------------------------

determinize :: TypeAut pol -> TypeAutDet pol
determinize aut =
  let
    starts = S.fromList aut.ta_starts
    newstart = M.findIndex starts newTransFun
    newTransFun = transFun aut.ta_core.ta_gr starts
    newTransFunReind = reIndexTransFun newTransFun
    newFlowEdges = flowEdges newTransFunReind aut.ta_core.ta_flowEdges
    newgr = newTypeGraph newTransFunReind aut.ta_core.ta_gr
    newCore = TypeAutCore { ta_gr = newgr, ta_flowEdges = newFlowEdges }
  in
    TypeAut { ta_pol = aut.ta_pol, ta_starts = Identity newstart, ta_core = newCore }


