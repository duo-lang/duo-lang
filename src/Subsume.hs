module Subsume
  ( isSubtype
  ) where

import Data.Graph.Inductive.Graph

import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Data.Maybe (fromJust)
import Data.Tuple (swap)
import Data.Bifunctor (bimap)
import Control.Monad.State

import Syntax.Types
import Syntax.TypeGraph

import Determinize (determinizeTypeAut)
import FlowAnalysis
import Minimize


-- Shift up all the nodes of the graph by the given number. Generates an isomorphic graph.
shiftGraph :: Int -> TypeAut -> TypeAut
shiftGraph shift (gr, starts, flowEdges) =
  ( mkGraph [(i + shift, a) | (i,a) <- labNodes gr] [(i + shift, j + shift, b) | (i,j,b) <- labEdges gr]
  , fmap (+shift) starts
  , bimap (+shift) (+shift) flowEdges)

-- Constructs the union of two TypeAuts, assumes that the node ranges don't overlap.
unsafeUnion :: TypeAut -> TypeAut -> TypeAut
unsafeUnion (gr1, starts1, flowEdges1) (gr2, starts2, flowEdges2) =
  ( mkGraph (labNodes gr1 ++ labNodes gr2) (labEdges gr1 ++ labEdges gr2)
  , starts1 ++ starts2
  , flowEdges1 ++ flowEdges2)

-- Constructs the union of two TypeAuts
typeAutUnion :: TypeAut -> TypeAut -> TypeAut
typeAutUnion aut1@(gr,_ ,_) aut2 = unsafeUnion aut1 (shiftGraph shift aut2)
  where
    shift = 1 + snd (nodeRange gr)

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
