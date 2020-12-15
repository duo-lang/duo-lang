module Syntax.TypeGraph where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Set (Set)
import qualified Data.Set as S
import Data.Bifunctor (bimap)
import Data.Functor.Identity
import Data.Containers.ListUtils (nubOrd)
import Syntax.Types
import Syntax.Terms

-------------------------------------------------------
-- Graph syntax
-------------------------------------------------------

data HeadCons = HeadCons
  { hc_data :: Maybe (Set XtorName)
  , hc_codata :: Maybe (Set XtorName)
  , hc_nominal :: Set TypeName
  } deriving (Eq,Show,Ord)

emptyHeadCons :: HeadCons
emptyHeadCons = HeadCons Nothing Nothing S.empty

singleHeadCons :: DataCodata -> Set XtorName -> HeadCons
singleHeadCons Data xtors = HeadCons (Just xtors) Nothing S.empty
singleHeadCons Codata xtors = HeadCons Nothing (Just xtors) S.empty

type NodeLabel = (PrdCns, HeadCons)

data EdgeLabel
  = EdgeSymbol DataCodata XtorName PrdCns Int
  deriving (Eq,Show, Ord)

type FlowEdge = (Node, Node)

type TypeGr = Gr NodeLabel EdgeLabel
type TypeGrEps = Gr NodeLabel (Maybe EdgeLabel)

typeGrToEps :: TypeGr -> TypeGrEps
typeGrToEps = emap Just


data TypeAut' a f = TypeAut
  { ta_gr :: Gr NodeLabel a
  , ta_starts :: f Node
  , ta_flowEdges :: [FlowEdge]
  }

type TypeAut       = TypeAut' EdgeLabel         []
type TypeAutDet    = TypeAut' EdgeLabel         Identity
type TypeAutEps    = TypeAut' (Maybe EdgeLabel) []
type TypeAutEpsDet = TypeAut' (Maybe EdgeLabel) Identity

class Nubable f where
  nub :: Ord a => f a -> f a
instance Nubable Identity where
  nub = id
instance Nubable [] where
  nub = nubOrd

-- Maps a function on nodes over a type automaton
mapTypeAut :: (Ord a, Functor f, Nubable f) => (Node -> Node) -> TypeAut' a f -> TypeAut' a f
mapTypeAut f TypeAut {..} = TypeAut
  { ta_gr = mkGraph (nub [(f i, a) | (i,a) <- labNodes ta_gr])
                    (nub [(f i , f j, b) | (i,j,b) <- labEdges ta_gr])
  , ta_starts = nub (f <$> ta_starts)
  , ta_flowEdges = nub (bimap f f <$> ta_flowEdges)
  }
