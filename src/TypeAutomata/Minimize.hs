module TypeAutomata.Minimize ( minimize ) where

import Data.Graph.Inductive.Graph ( lab, lpre, nodes, Graph(labEdges), Node )
import Data.List (intersect, (\\), partition)
import Data.Maybe (fromMaybe, catMaybes, fromJust)

import Data.Set (Set)
import Data.Set qualified as S
import qualified Data.Map as M

import TypeAutomata.Definition
import Syntax.Common.Polarity ( Polarity(..) )


getAlphabet :: TypeGr -> [EdgeLabelNormal]
getAlphabet gr = nub $ map (\(_,_,b) -> b) (labEdges gr)

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

minimize' :: Preds -> [EdgeLabelNormal] -> [EquivalenceClass] -> [EquivalenceClass] -> [EquivalenceClass]
minimize' _preds _alph []     ps = ps
minimize' preds  alph  (w:ws) ps = minimize' preds alph ws' ps'
  where
    (ws',ps') = refineAllLetters alph (ws, w:ps)

    refineAllLetters :: [EdgeLabelNormal] -> ([EquivalenceClass], [EquivalenceClass]) -> ([EquivalenceClass], [EquivalenceClass])
    refineAllLetters []       acc = acc
    refineAllLetters (a:alph) (ws,ps) = let pre       = predsWith preds w a
                                            (ws',ps') = refinePs pre ps ([],[])
                                            ws''      = refineWaiting pre ws
                                        in refineAllLetters alph (ws' ++ ws'', ps')

    refinePs :: [Node] -> [EquivalenceClass] -> ([EquivalenceClass], [EquivalenceClass]) -> ([EquivalenceClass], [EquivalenceClass])
    refinePs _pre []      acc       = acc
    refinePs pre  (p:ps)  (ws',ps') = let (p1, p2, n1, n2) = splitPs pre p ([], [], 0, 0)
                                          (p1', p2')       = if n1 < n2 then (p1, p2) else (p2, p1)
                                          ws''             = if null p1' then ws' else p1':ws'
                                          ps''             = p2' : ps'
                                      in refinePs pre ps (ws'',ps'')
    -- TODO: use fact this is sorted
    splitPs :: [Node] -> EquivalenceClass -> (EquivalenceClass, EquivalenceClass, Int, Int) -> (EquivalenceClass, EquivalenceClass, Int, Int)
    splitPs _pre [] acc                          = acc
    splitPs pre (p:ps) (inter,diff,ninter,ndiff) = let acc = if p `elem` pre
                                                             then (p:inter, diff  , ninter+1, ndiff)
                                                             else (inter  , p:diff, ninter  , ndiff+1)
                                                    in  splitPs pre ps acc

    refineWaiting :: [Node] -> [EquivalenceClass] -> [EquivalenceClass]
    refineWaiting _pre [] = []
    refineWaiting pre (l:ls) = splitLs pre l ++ refineWaiting pre ls

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

-- We don't have a direct notion for accepting states, so we unroll the definition of the
-- minimisation algorithm once
initialSplit :: TypeAutCore EdgeLabelNormal -> ([EquivalenceClass], [EquivalenceClass])
initialSplit aut@TypeAutCore { ta_gr } = (rest,catMaybes [posMin,negMin])
  where
    distGroups = myGroupBy (equalNodes aut) (nodes ta_gr)
    (posMin,negMin,rest) = getMins distGroups
  
    getMins :: [EquivalenceClass]
            -> (Maybe EquivalenceClass, Maybe EquivalenceClass, [EquivalenceClass])
    getMins []                 = (Nothing, Nothing, [])
    getMins ([]        : _iss) = error "Minimize: Empty equivalence class should not exist"
    getMins (eq@(nd : _) : iss)  =
      let l = fromJust $ lab ta_gr nd
          pol = getLabelPol l
          (p,n,iss') = getMins iss
          (p',n',iss'')  = case (pol, p, n) of
                            (Pos, Nothing, _) -> (Just eq, n, iss')
                            (Pos, Just ns, _) ->
                              if length ns > length eq
                              then (Just eq, n, ns : iss')
                              else (Just ns, n, eq : iss')
                            (Neg, _, Nothing) -> (p, Just eq, iss')
                            (Neg, _, Just ns) ->
                              if length ns > length eq
                              then (p, Just eq, ns : iss')
                              else (p, Just ns, eq : iss')
      in (p', n', iss'')

getLabelPol :: NodeLabel -> Polarity
getLabelPol MkNodeLabel {nl_pol} = nl_pol
getLabelPol MkPrimitiveNodeLabel {pl_pol} = pl_pol

-- generate a function that maps each node to the representative of its respective equivalence class
genMinimizeFun :: TypeAutCore EdgeLabelNormal -> (Node -> Node)
genMinimizeFun aut@TypeAutCore { ta_gr } = getNewNode
  where
    preds = predsMap ta_gr
    alph = getAlphabet ta_gr
    --  distGroups = myGroupBy (equalNodes aut) (nodes ta_gr)
    --  (pos,neg) = splitByPolarity aut
    (ls,ps) = initialSplit aut
    nodeSets = minimize' preds alph ls ps
    getNewNode n = head $ head $ filter (n `elem`) nodeSets

minimize :: TypeAutDet pol -> TypeAutDet pol
minimize aut@TypeAut {ta_core} = aut'
  where
    ta_core' = removeRedundantEdgesCore ta_core
    fun = genMinimizeFun ta_core'
    aut' = mapTypeAut fun aut
