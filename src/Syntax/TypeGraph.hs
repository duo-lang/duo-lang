{-# LANGUAGE RecordWildCards #-}
module Syntax.TypeGraph where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Set (Set)
import Data.Bifunctor (bimap)
import Data.Containers.ListUtils (nubOrd)

import Syntax.Types
import Syntax.Terms

-------------------------------------------------------
-- Graph syntax
-------------------------------------------------------

data HeadCons = HeadCons
  { hc_data :: Maybe (Set XtorName)
  , hc_codata :: Maybe (Set XtorName)
  } deriving (Eq,Show,Ord)

emptyHeadCons :: HeadCons
emptyHeadCons = HeadCons Nothing Nothing

singleHeadCons :: DataOrCodata -> Set XtorName -> HeadCons
singleHeadCons Data xtors = HeadCons (Just xtors) Nothing
singleHeadCons Codata xtors = HeadCons Nothing (Just xtors)

type NodeLabel = (Polarity, HeadCons)

data EdgeLabel
  = EdgeSymbol DataOrCodata XtorName PrdOrCns Int
  deriving (Eq,Show)

instance Ord EdgeLabel where
  compare (EdgeSymbol _ _ _ x) (EdgeSymbol _ _ _ y) = compare x y

type FlowEdge = (Node, Node)

type TypeGr = Gr NodeLabel EdgeLabel
type TypeGrEps = Gr NodeLabel (Maybe EdgeLabel)

typeGrToEps :: TypeGr -> TypeGrEps
typeGrToEps = emap Just

data TypeAut = TypeAut
  { ta_gr :: TypeGr
  , ta_starts :: [Node]
  , ta_flowEdges :: [FlowEdge]
  }

-- Maps a function on nodes over a type automaton
mapTypeAut :: (Node -> Node) -> TypeAut -> TypeAut
mapTypeAut f TypeAut {..} = TypeAut
  { ta_gr = mkGraph (nubOrd [(f i, a) | (i,a) <- labNodes ta_gr])
                    (nubOrd [(f i , f j, b) | (i,j,b) <- labEdges ta_gr])
  , ta_starts = nubOrd (f <$> ta_starts)
  , ta_flowEdges = nubOrd (bimap f f <$> ta_flowEdges)
  }
