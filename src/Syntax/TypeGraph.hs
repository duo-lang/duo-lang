module Syntax.TypeGraph where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Set (Set)
import qualified Data.Set as S
import Data.Bifunctor (bimap)
import Data.Functor.Identity
import Data.Containers.ListUtils (nubOrd)
import Data.Void
import Syntax.Types
import Syntax.CommonTerm

-------------------------------------------------------
-- Graph syntax
-------------------------------------------------------

data NodeLabel = HeadCons
  { hc_pol :: Polarity
  , hc_data :: Maybe (Set XtorName)
  , hc_codata :: Maybe (Set XtorName)
  , hc_nominal :: Set TypeName
  } deriving (Eq,Show,Ord)

emptyHeadCons :: Polarity -> NodeLabel
emptyHeadCons pol = HeadCons pol Nothing Nothing S.empty

singleHeadCons :: Polarity -> DataCodata -> Set XtorName -> NodeLabel
singleHeadCons pol Data xtors   = HeadCons pol (Just xtors) Nothing S.empty
singleHeadCons pol Codata xtors = HeadCons pol Nothing (Just xtors) S.empty

data EdgeLabel a
  = EdgeSymbol DataCodata XtorName Polarity Int
  | EpsilonEdge a
  deriving (Eq,Show, Ord)

type EdgeLabelNormal  = EdgeLabel Void
type EdgeLabelEpsilon = EdgeLabel ()

embedEdgeLabel :: EdgeLabelNormal -> EdgeLabelEpsilon
embedEdgeLabel (EdgeSymbol dc xt pc i) = EdgeSymbol dc xt pc i
embedEdgeLabel (EpsilonEdge v) = absurd v

unsafeEmbedEdgeLabel :: EdgeLabelEpsilon -> EdgeLabelNormal
unsafeEmbedEdgeLabel (EdgeSymbol dc xt pc i) = EdgeSymbol dc xt pc i
unsafeEmbedEdgeLabel (EpsilonEdge _) = error "unsafeEmbedEdgeLabel failed"

type FlowEdge = (Node, Node)

type TypeGr = Gr NodeLabel EdgeLabelNormal
type TypeGrEps = Gr NodeLabel EdgeLabelEpsilon

data TypeAut' a f = TypeAut
  { ta_gr :: Gr NodeLabel a
  , ta_starts :: f Node
  , ta_flowEdges :: [FlowEdge]
  }
deriving instance Show TypeAut
deriving instance Show TypeAutDet
deriving instance Show TypeAutEps
deriving instance Show TypeAutEpsDet

type TypeAut       = TypeAut' EdgeLabelNormal  []
type TypeAutDet    = TypeAut' EdgeLabelNormal  Identity
type TypeAutEps    = TypeAut' EdgeLabelEpsilon []
type TypeAutEpsDet = TypeAut' EdgeLabelEpsilon Identity

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
