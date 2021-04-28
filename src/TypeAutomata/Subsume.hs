module TypeAutomata.Subsume
  ( isSubtype
  , typeAutEqual
  ) where

import Data.Graph.Inductive.Graph

import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Data.Maybe (fromJust)
import Data.Tuple (swap)
import Data.Functor.Identity
import Control.Monad.State

import Syntax.Types
import Syntax.TypeAutomaton

import TypeAutomata.Determinize (determinize)
import TypeAutomata.RemoveAdmissible
import TypeAutomata.Minimize (minimize)


-- Shift up all the nodes of the graph by the given number. Generates an isomorphic graph.
shiftGraph :: Int -> TypeAutDet pol -> TypeAutDet pol
shiftGraph shift = mapTypeAut (+shift)

-- Constructs the union of two TypeAuts, assumes that the node ranges don't overlap.
unsafeUnion :: TypeAutDet pol -> TypeAutDet pol -> TypeAut pol
unsafeUnion (TypeAut polrep gr1 (Identity starts1) flowEdges1) (TypeAut _ gr2 (Identity starts2) flowEdges2) =
  TypeAut { ta_pol = polrep
          , ta_gr = mkGraph (labNodes gr1 ++ labNodes gr2) (labEdges gr1 ++ labEdges gr2)
          , ta_starts = [starts1, starts2]
          , ta_flowEdges = flowEdges1 ++ flowEdges2
          }

-- Constructs the union of two TypeAuts
typeAutUnion :: TypeAutDet pol -> TypeAutDet pol -> TypeAut pol
typeAutUnion aut1@TypeAut{..} aut2 = unsafeUnion aut1 (shiftGraph shift aut2)
  where
    shift = 1 + snd (nodeRange ta_gr)

isSubtype :: TypeAutDet pol -> TypeAutDet pol -> Bool
isSubtype aut1 aut2 = case (startPolarity aut1, startPolarity aut2) of
  (Pos,Pos) -> fun (typeAutUnion aut1 aut2) `typeAutEqual` aut2
  (Neg,Neg) -> fun (typeAutUnion aut1 aut2) `typeAutEqual` aut1
  _         -> error "isSubtype: only defined for types of equal polarity."
  where
    startPolarity TypeAut{..} = hc_pol (fromJust (lab ta_gr (runIdentity ta_starts)))
    fun = minimize . removeAdmissableFlowEdges . determinize

typeAutEqual :: TypeAutDet pol -> TypeAutDet pol -> Bool
typeAutEqual (TypeAut _ gr1 (Identity start1) flowEdges1) (TypeAut _ gr2 (Identity start2) flowEdges2)
  = case runStateT (typeAutEqualM (gr1, start1) (gr2, start2)) M.empty of
      Nothing -> False
      Just ((),mp) ->
        S.fromList flowEdges2 ==
          S.fromList [(i',j') | (i,j) <- flowEdges1, let Just i' = M.lookup i mp, let Just j' = M.lookup j mp]

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
