module TypeAutomata.Minimize ( minimize ) where

import Data.Graph.Inductive.Graph
import Data.List (intersect, (\\), delete, partition)
import Data.Maybe (fromMaybe, catMaybes, fromJust)

import Data.Set (Set)
import Data.Set qualified as S
import qualified Data.Map as M

import TypeAutomata.Definition
import Syntax.Common (RnTypeName, PrimitiveType, Polarity(..), Variance)


getAlphabet :: TypeGr -> [EdgeLabelNormal]
getAlphabet gr = nub $ map (\(_,_,b) -> b) (labEdges gr)

data Alphabet where
  AData         :: Polarity -> XtorLabel                   -> Alphabet
  ACodata       :: Polarity -> XtorLabel                   -> Alphabet
  ANominal      :: Polarity -> (RnTypeName, [Variance])    -> Alphabet
  ARefinementD  :: Polarity -> (RnTypeName, Set XtorLabel) -> Alphabet
  ARefinementCD :: Polarity -> (RnTypeName, Set XtorLabel) -> Alphabet
  APrimitive    :: Polarity -> PrimitiveType               -> Alphabet
    deriving (Eq,Ord)

getLabels :: TypeGr -> [Alphabet]
getLabels gr = nub $ concat $ catMaybes allLabels
  where
    ns = nodes gr

    allLabels :: [Maybe [Alphabet]]
    allLabels = fmap labelToAlphabet . lab gr <$> ns

    labelToAlphabet :: NodeLabel -> [Alphabet]
    labelToAlphabet MkNodeLabel {..} =
        let aData      = maybe [] (fmap (AData nl_pol) . S.toList)   nl_data
            aCodata    = maybe [] (fmap (ACodata nl_pol) . S.toList) nl_codata
            aNominal   = (ANominal nl_pol) <$> S.toList nl_nominal
            aRefData   = ARefinementD  nl_pol <$> M.toList nl_ref_data
            aRefCodata = ARefinementCD nl_pol <$> M.toList nl_ref_codata
        in aData ++ aCodata ++ aNominal ++ aRefData ++ aRefCodata
    labelToAlphabet MkPrimitiveNodeLabel {..} = [ APrimitive pl_pol pl_prim ]

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
minimize' preds  alph  (d:ds) ps =
  let newDs = delete d (foldl (flip (splitAlong preds d)) (d:ds) alph)
      newPs =           foldl (flip (splitAlong preds d)) ps     alph
  in  minimize' preds alph newDs newPs

-- an implementation of Hopcroft's minimisation algorithm
-- with simplifications found in
-- Re-describing an algorithm by Hopcroft (Timo Knuutila, 2001)
-- the original Hopcroft
-- 𝑄/𝜌 ← {𝐹, 𝑄 ⧵ 𝐹}
-- 𝐿 ← {𝐹}
-- while there exists 𝐴 ∈ 𝐿 do
--    𝐿 ← 𝐿 ⧵ {𝐴}
--    for each 𝑥 ∈ Σ do
--      let 𝑋 = 𝛿−1
--      𝑥 (𝐴)
--      for each 𝑌 ∈ 𝑄/𝜌 s.t. (𝑌 ′ = 𝑌 ∩ 𝑋 ≠ ∅) ∧ (𝑌 ″ = 𝑌 ⧵ 𝑋 ≠ ∅) do
--        𝑄/𝜌 ← (𝑄/𝜌 ⧵ {𝑌}) ∪ {𝑌 ′, 𝑌 ″}
--        if 𝑌 ∈ 𝐿 then
--          𝐿 ← (𝐿 ⧵ {𝑌}) ∪ {𝑌 ′, 𝑌 ″}
--        else
--          𝐿 ← 𝐿 ∪ {min(𝑌 ′, 𝑌 ″)}
--      end
--    end
-- end
--
-- becomes the following variant (since 𝐿 ⊆ 𝑄/𝜌 is a loop invariant)
--
-- Let 𝑅 = 𝑄/𝜌 ⧵ 𝐿
--  𝑅 ← {𝑄 ⧵ 𝐹}
--  𝐿 ← {𝐹}
--    while there exists 𝐴 ∈ 𝐿 do
--      𝐿 ← 𝐿 ⧵ {𝐴}
--      𝑅 ← 𝑅 ∪ {𝐴}
--      for each 𝑥 ∈ Σ do
--        let 𝑋 = 𝛿−1_𝑥 (𝐴)
--        for each 𝑌 ∈ 𝑅 s.t. (𝑌 ′ = 𝑌 ∩ 𝑋 ≠ ∅) ∧ (𝑌 ″ = 𝑌 ⧵ 𝑋 ≠ ∅) do
--          𝑅 ← (𝑅 ⧵ {𝑌}) ∪ {max(𝑌 ′, 𝑌 ″)}
--          𝐿 ← 𝐿 ∪ {min(𝑌 ′, 𝑌 ″)}
--        end
--        for each 𝑌 ∈ 𝐿 s.t. (𝑌 ′ = 𝑌 ∩ 𝑋 ≠ ∅) ∧ (𝑌 ″ = 𝑌 ⧵ 𝑋 ≠ ∅) do
--          𝐿 ← (𝐿 ⧵ {𝑌}) ∪ {𝑌 ′, 𝑌 ″}
--      end
--    end
--  end

type EquivalenceClass = [Node]

minimize'' :: Preds -> [EdgeLabelNormal] -> [EquivalenceClass] -> [EquivalenceClass] -> [EquivalenceClass]
minimize'' _preds _alph []     ps = ps
minimize'' preds  alph  (l:ls) ps = minimize'' preds alph ls' ps'
  where
    (ps',ls') = refinePs alph (ps, ls)
    refinePs :: [EdgeLabelNormal] -> ([EquivalenceClass], [EquivalenceClass]) -> ([EquivalenceClass], [EquivalenceClass])
    refinePs []       acc = acc
    refinePs (a:alph) (ps,ls) = let pre = predsWith preds l a
                                    (ps',ls') = refinePs' pre ps ([],ls)
                                    ls'' = refineLs pre ls
                                in refinePs alph (ps',ls' ++ ls'')

    refinePs' :: [Node] -> [EquivalenceClass] -> ([EquivalenceClass], [EquivalenceClass]) -> ([EquivalenceClass], [EquivalenceClass])
    refinePs' _pre []      acc       = acc
    refinePs' pre  (p:ps)  (ps',ls') = let (p1, p2, n1, n2) = splitPs pre p ([], [], 0, 0)
                                           (p1', p2') = if n1 < n2 then (p1, p2) else (p2, p1)
                                           ls''     = if null p1' then ls' else p1':ls'
                                           ps''     = p2' : ps'
                                      in refinePs' pre ps (ps'',ls'')
    -- TODO: use fact this is sorted
    splitPs :: [Node] -> EquivalenceClass -> (EquivalenceClass, EquivalenceClass, Int, Int) -> (EquivalenceClass, EquivalenceClass, Int, Int)
    splitPs pre [] acc                           = acc
    splitPs pre (p:ps) (inter,diff,ninter,ndiff) = let acc = if p `elem` pre
                                                             then (p:inter, diff  , ninter+1, ndiff)
                                                             else (inter  , p:diff, ninter  , ndiff+1)
                                                   in  splitPs pre ps acc

    refineLs :: [Node] -> [EquivalenceClass] -> [EquivalenceClass]
    refineLs _pre [] = []
    refineLs pre (l:ls) = splitLs pre l ++ refineLs pre ls

    splitLs :: [Node] -> EquivalenceClass -> [EquivalenceClass]
    splitLs pre l = let (l1,l2) = (l `intersect` pre, l \\ pre)
                    in if null l1 || null l2 then [l] else [l1, l2]

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

splitByPolarity :: TypeAutCore EdgeLabelNormal -> (EquivalenceClass, EquivalenceClass)
splitByPolarity TypeAutCore {ta_gr} = (pos, neg)
  where
    ns = (\x -> (x, fromJust $ lab ta_gr x)) <$> nodes ta_gr
    pos = fst <$> filter (\(_,l) -> Pos == getPol l) ns
    neg = fst <$> filter (\(_,l) -> Neg == getPol l) ns
    getPol :: NodeLabel -> Polarity
    getPol MkNodeLabel {nl_pol} = nl_pol
    getPol MkPrimitiveNodeLabel {pl_pol} = pl_pol

-- generate a function that maps each node to the representative of its respective equivalence class
genMinimizeFun :: TypeAutCore EdgeLabelNormal -> (Node -> Node)
genMinimizeFun aut@TypeAutCore { ta_gr } = getNewNode
  where
    distGroups = myGroupBy (equalNodes aut) (nodes ta_gr)
    nodeSets = minimize' (predsMap ta_gr) (getAlphabet ta_gr) distGroups distGroups
    (pos,neg) = splitByPolarity aut
    getNewNode n = head $ head $ filter (n `elem`) nodeSets

minimize :: TypeAutDet pol -> TypeAutDet pol
minimize aut@TypeAut {ta_core} = aut'
  where
    ta_core' = removeRedundantEdgesCore ta_core
    fun = genMinimizeFun ta_core'
    aut' = mapTypeAut fun aut


