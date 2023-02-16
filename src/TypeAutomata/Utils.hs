
module TypeAutomata.Utils
  ( typeAutEqual
  , typeAutIsEmpty
  , isEmptyLabel
  ) where

import Data.Map (Map)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (fromJust,isNothing)
import Data.Tuple (swap)
import Data.Graph.Inductive.Graph (Node, lab, lsuc, DynGraph, Graph (..))

import Control.Monad.Identity (Identity(..))
import Control.Monad.State (StateT(runStateT), MonadTrans (..))
import Control.Monad.State.Class ( MonadState(..), modify )
import Control.Monad ( guard, forM_ )

import TypeAutomata.Definition (TypeAutDet, TypeAut' (..), TypeAutCore (..), TypeGr, NodeLabel (..))

typeAutEqual :: TypeAutDet pol -> TypeAutDet pol -> Bool
typeAutEqual (TypeAut _ (Identity start1) (TypeAutCore gr1 flowEdges1))
             (TypeAut _ (Identity start2) (TypeAutCore gr2 flowEdges2))
  = case runStateT (typeAutEqualM (gr1, start1) (gr2, start2)) M.empty of
      Nothing -> False
      Just ((),mp) ->
        S.fromList flowEdges2 ==
          S.fromList [(i',j') | (i,j) <- flowEdges1, let i' = fromJust (M.lookup i mp), let j' = fromJust (M.lookup j mp)]

typeAutEqualM :: (TypeGr, Node) -> (TypeGr, Node) -> StateT (Map Node Node) Maybe ()
typeAutEqualM (gr1, n) (gr2, m) = do
  mp <- get
  case M.lookup n mp of
    Nothing -> do
      guard (lab gr1 n== lab gr2 m)
      modify (M.insert n m)
      forM_ (lsuc gr1 n) $ \(i,el) -> do
        j <- lift $ sucWith gr2 m el
        typeAutEqualM (gr1, i) (gr2, j)
    Just m' -> do
      guard (m == m')

sucWith :: (DynGraph gr, Eq b) => gr a b -> Node -> b -> Maybe Node
sucWith gr i el = lookup el (map swap (lsuc gr i))

isEmptyLabel :: NodeLabel -> Bool
isEmptyLabel nl
             = nothingOrEmpty nl.nl_data && nothingOrEmpty nl.nl_codata && S.null nl.nl_nominal && mapNull (fst nl.nl_ref_data) && mapNull (fst nl.nl_ref_codata) && isNothing (snd nl.nl_ref_data) && isNothing (snd nl.nl_ref_codata)
  where nothingOrEmpty Nothing = True
        nothingOrEmpty (Just s) = S.null s
        mapNull = M.foldr (\x y -> S.null x && y) True
isEmptyLabel _ = False

-- | Check whether all labels in an automaton are empty.
typeAutIsEmpty :: forall pol. TypeAutDet pol -> Bool
typeAutIsEmpty (TypeAut _ (Identity _) (TypeAutCore gr _)) = all (isEmptyLabel . snd) (labNodes gr)
