module TypeAutomata.Minimize ( minimize ) where

import Data.Graph.Inductive.Graph
import Data.List (intersect, (\\), delete, partition)

import Data.Set (Set)
import Data.Set qualified as S

import TypeAutomata.Definition


getAlphabet :: TypeGr -> [EdgeLabelNormal]
getAlphabet gr = nub $ map (\(_,_,b) -> b) (labEdges gr)

predsWith :: TypeGr -> [Node] -> EdgeLabelNormal -> [Node]
predsWith gr ns x = nub . map fst . filter ((==x).snd) . concat $ map (lpre gr) ns

splitAlong :: TypeGr -> [Node] -> EdgeLabelNormal -> [[Node]] -> [[Node]]
splitAlong gr ds x ps = do
  let re = predsWith gr ds x
  p <- ps
  let (p1,p2) = (p `intersect` re, p \\ re)
  if null p1 || null p2 then [p] else [p1,p2]

minimize' :: TypeGr -> [[Node]] -> [[Node]] -> [[Node]]
minimize' _ [] ps = ps
minimize' gr (d:ds) ps = minimize' gr (delete d (foldr (splitAlong gr d) (d:ds) (getAlphabet gr)))
                                      (foldr (splitAlong gr d) ps (getAlphabet gr))

myGroupBy :: (a -> a -> Bool) -> [a] -> [[a]]
myGroupBy _ [] = []
myGroupBy p (x:xs) = let (xs1,xs2) = partition (p x) xs in (x:xs1) : myGroupBy p xs2

-- | 
flowNeighbors :: TypeGr -> Node -> Set Node
flowNeighbors ta_gr i =
  S.fromList $ [right | (left,right, FlowEdge) <- labEdges ta_gr , i == left] ++ [left | (left,right,FlowEdge) <- labEdges ta_gr, i == right]

equalNodes :: TypeGr -> Node -> Node -> Bool
equalNodes ta_gr i j =
  (lab ta_gr i == lab ta_gr j) && flowNeighbors ta_gr i == flowNeighbors ta_gr j

genMinimizeFun :: TypeGr -> (Node -> Node)
genMinimizeFun ta_gr = getNewNode
  where
    distGroups = myGroupBy (equalNodes ta_gr) (nodes ta_gr)
    nodeSets = minimize' ta_gr distGroups distGroups
    getNewNode n = head $ head $ filter (n `elem`) nodeSets

minimize :: TypeAutDet pol -> TypeAutDet pol
minimize aut@TypeAut { ta_graph } = removeRedundantEdgesAut aut'
  where
    ta_graph' = removeRedundantEdges ta_graph
    fun = genMinimizeFun ta_graph'
    aut' = mapTypeAut fun aut


