module Subsume where

  import Data.Graph.Inductive.Graph

  import qualified Data.Set as S

  import Data.Map (Map)
  import qualified Data.Map as M

  import Data.Maybe (fromJust)
  import Data.Tuple (swap)
  import Data.Bifunctor (bimap)
  import Control.Monad.State

  import Syntax.Terms
  import Syntax.Types
  import Syntax.TypeGraph

  import Determinize (determinizeTypeAut)
  import FlowAnalysis
  import Minimize

  typeAutUnion :: TypeAut -> TypeAut -> TypeAut
  typeAutUnion (gr1, starts1, flowEdges1) (gr2, starts2, flowEdges2) = (
      mkGraph (labNodes gr1 ++ [(i + n0, a) | (i,a) <- labNodes gr2])
              (labEdges gr1 ++ [(i+n0,j+n0,b) | (i,j,b) <- labEdges gr2])
    , starts1 ++ map (+n0) starts2
    , flowEdges1 ++ map (bimap (+n0) (+n0)) flowEdges2)
    where
      n0 = 1 + snd (nodeRange gr1)

  isSubtype :: TypeAut -> TypeAut -> Bool
  isSubtype aut1 aut2 = case (startPolarity aut1, startPolarity aut2) of
    (Pos,Pos) -> (minimizeTypeAut . removeAdmissableFlowEdges . determinizeTypeAut) (typeAutUnion aut1 aut2) `typeAutEqual` aut2
    (Neg,Neg) -> (minimizeTypeAut . removeAdmissableFlowEdges . determinizeTypeAut) (typeAutUnion aut1 aut2) `typeAutEqual` aut1
    _         -> error "isSubtype: only defined for types of equal polarity."
    where
      startPolarity (gr,[start],_) = fst (fromJust (lab gr start))


  typeAutEqual :: TypeAut -> TypeAut -> Bool
  typeAutEqual (gr1, [start1], flowEdges1) (gr2, [start2], flowEdges2)
    = case runStateT (typeAutEqualM (gr1, start1) (gr2, start2)) M.empty of
        Nothing -> False
        Just ((),mp) ->
          S.fromList flowEdges2 ==
            S.fromList [(i',j') | (i,j) <- flowEdges1, let Just i' = M.lookup i mp, let Just j' = M.lookup j mp]
  typeAutEqual _ _ = error "typeAutEqual: only defined for deterministic automata!"

  sucWith :: (DynGraph gr, Eq b) => gr a b -> Node -> b -> Maybe Node
  sucWith gr i el = lookup el (map swap (lsuc gr i))

  typeAutEqualM :: (TypeGr, Node) -> (TypeGr, Node) -> StateT (Map Node Node) Maybe ()
  typeAutEqualM (gr1, n) (gr2, m) = do
    mp <- get
    case M.lookup n mp of
      Nothing -> do
        guard (lab gr1 n == lab gr2 m)
        modify (M.insert n m)
        forM_ (lsuc gr1 n) $ \(i,el) -> do
          j <- lift $ sucWith gr2 m el
          typeAutEqualM (gr1, i) (gr2, j)
      Just m' -> do
        guard (m == m')
