module TypeAutomata.Minimize ( minimize ) where

import Data.Graph.Inductive.Graph
import Data.List (intersect, (\\), delete, partition)

import Data.Set (Set)
import qualified Data.Set as S

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

flowNeighbors :: TypeAutCore EdgeLabelNormal -> Node -> Set Node
flowNeighbors TypeAutCore { ta_flowEdges } i =
  S.fromList $ [n | (j,n) <- ta_flowEdges, i == j] ++ [n | (n,j) <- ta_flowEdges, i == j]

equalNodes :: TypeAutCore EdgeLabelNormal -> Node -> Node -> Bool
equalNodes aut@TypeAutCore{ ta_gr } i j =
  (lab ta_gr i == lab ta_gr j) && flowNeighbors aut i == flowNeighbors aut j


-- note: nodes with different labels or different flow edge behaviour are never merged
minimizeCore :: TypeAutCore EdgeLabelNormal -> TypeAutCore EdgeLabelNormal
minimizeCore aut@TypeAutCore { ta_gr } =
  let
    gr' = removeRedundantEdges ta_gr
    distGroups = myGroupBy (equalNodes aut) (nodes gr')
    nodeSets = minimize' gr' distGroups distGroups
    getNewNode n = head $ head $ filter (n `elem`) nodeSets
  in
    mapTypeAutCore getNewNode aut


minimize :: TypeAutDet pol -> TypeAutDet pol
minimize aut@TypeAut{ ta_core } = removeRedundantEdgesAut (aut { ta_core = minimizeCore ta_core })

