module TypeAutomata.Minimize ( minimize ) where

import Data.Graph.Inductive.Graph
import Data.List (intersect, (\\), delete, partition)
import Data.Maybe (fromMaybe)

import Data.Set (Set)
import Data.Set qualified as S
import qualified Data.Map as M

import TypeAutomata.Definition


getAlphabet :: TypeGr -> [EdgeLabelNormal]
getAlphabet gr = nub $ map (\(_,_,b) -> b) (labEdges gr)

-- find all predecessors with connecting edge labelled by specified label
predsWith' :: TypeGr -> [Node] -> EdgeLabelNormal -> [Node]
predsWith' gr ns x = nub . map fst . filter ((==x).snd) $ concatMap (lpre gr) ns

type Preds = M.Map (Node,EdgeLabelNormal) [Node]

-- find all predecessors with connecting edge labelled by specified label
predsWith :: Preds -> [Node] -> EdgeLabelNormal -> [Node]
predsWith preds ns x = nub $ concatMap (\n -> fromMaybe [] $ M.lookup (n,x) preds) ns

predsMap :: TypeGr -> Preds
predsMap gr =
  let alph  = getAlphabet gr
      ns    = nodes gr

      preds :: M.Map Node [(Node,EdgeLabelNormal)]
      preds = M.fromList $ fmap(\n -> (n, lpre gr n)) ns

      getPred :: Node -> EdgeLabelNormal -> [Node]
      getPred n l = map fst . filter ((== l) . snd) $ fromMaybe [] $ M.lookup n preds

      addCharNode :: EdgeLabelNormal -> Preds -> Node -> Preds
      addCharNode a m n = M.insert (n,a) (getPred n a) m

      addChar :: Preds -> EdgeLabelNormal -> Preds
      addChar m a = foldl (addCharNode a) m ns

  in  foldl addChar M.empty alph

splitAlong :: Preds -> [Node] -> EdgeLabelNormal -> [[Node]] -> [[Node]]
splitAlong preds ds x ps = do
  let re = predsWith preds ds x
  p <- ps
  let (p1,p2) = (p `intersect` re, p \\ re)
  if null p1 || null p2 then [p] else [p1,p2]

-- minimize by refining the equivalence
-- this is done by taking refining the second partition an refining it via the first one
minimize' :: Preds -> [EdgeLabelNormal] -> [[Node]] -> [[Node]] -> [[Node]]
minimize' _preds _alph []     ps = ps
minimize' preds  alph  (d:ds) ps = minimize' preds alph (delete d (foldl (flip (splitAlong preds d)) (d:ds) alph))
                                                                  (foldl (flip (splitAlong preds d)) ps     alph)

-- partition list by equivalence (given as a function)
myGroupBy :: (a -> a -> Bool) -> [a] -> [[a]]
myGroupBy _ [] = []
myGroupBy p (x:xs) = let (xs1,xs2) = partition (p x) xs in (x:xs1) : myGroupBy p xs2

flowNeighbors :: TypeAutCore EdgeLabelNormal -> Node -> Set Node
flowNeighbors TypeAutCore { ta_flowEdges } i =
  S.fromList $ [n | (j,n) <- ta_flowEdges, i == j] ++ [n | (n,j) <- ta_flowEdges, i == j]

-- nodes are considered equal if they have the same label and the same neighbors along flow edges
equalNodes :: TypeAutCore EdgeLabelNormal -> Node -> Node -> Bool
equalNodes aut@TypeAutCore{ ta_gr } i j =
  (lab ta_gr i == lab ta_gr j) && flowNeighbors aut i == flowNeighbors aut j

-- generate a function that maps each node to the representative of its respective equivalence class
genMinimizeFun :: TypeAutCore EdgeLabelNormal -> (Node -> Node)
genMinimizeFun aut@TypeAutCore { ta_gr } = getNewNode
  where
    distGroups = myGroupBy (equalNodes aut) (nodes ta_gr)
    nodeSets = minimize' (predsMap ta_gr) (getAlphabet ta_gr) distGroups distGroups
    getNewNode n = head $ head $ filter (n `elem`) nodeSets

minimize :: TypeAutDet pol -> TypeAutDet pol
minimize aut@TypeAut {ta_core} = aut'
  where
    ta_core' = removeRedundantEdgesCore ta_core
    fun = genMinimizeFun ta_core'
    aut' = mapTypeAut fun aut


