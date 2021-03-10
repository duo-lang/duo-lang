module Syntax.TypeAutomaton where

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

newtype XtorLabel = XtorLabel { labelName :: XtorName }
  deriving (Eq, Show, Ord)

data NodeLabel = HeadCons
  { hc_pol :: Polarity
  , hc_data :: Maybe (Set XtorLabel)
  , hc_codata :: Maybe (Set XtorLabel)
  , hc_nominal :: Set TypeName
  } deriving (Eq,Show,Ord)

emptyHeadCons :: Polarity -> NodeLabel
emptyHeadCons pol = HeadCons pol Nothing Nothing S.empty

singleHeadCons :: Polarity -> DataCodata -> Set XtorLabel -> NodeLabel
singleHeadCons pol Data xtors   = HeadCons pol (Just xtors) Nothing S.empty
singleHeadCons pol Codata xtors = HeadCons pol Nothing (Just xtors) S.empty

data EdgeLabel a
  = EdgeSymbol DataCodata XtorName PrdCns Int
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

data TypeAut' a f (pol :: Polarity) = TypeAut
  { ta_pol :: PolarityRep pol
  , ta_gr :: Gr NodeLabel a
  , ta_starts :: f Node
  , ta_flowEdges :: [FlowEdge]
  }
deriving instance Show (TypeAut pol)
deriving instance Show (TypeAutDet pol)
deriving instance Show (TypeAutEps pol)
deriving instance Show (TypeAutEpsDet pol)

type TypeAut pol       = TypeAut' EdgeLabelNormal  [] pol
type TypeAutDet pol    = TypeAut' EdgeLabelNormal  Identity pol
type TypeAutEps pol    = TypeAut' EdgeLabelEpsilon [] pol
type TypeAutEpsDet pol = TypeAut' EdgeLabelEpsilon Identity pol

class Nubable f where
  nub :: Ord a => f a -> f a
instance Nubable Identity where
  nub = id
instance Nubable [] where
  nub = nubOrd

-- Maps a function on nodes over a type automaton
mapTypeAut :: (Ord a, Functor f, Nubable f) => (Node -> Node) -> TypeAut' a f pol -> TypeAut' a f pol
mapTypeAut f TypeAut {..} = TypeAut
  { ta_pol = ta_pol
  , ta_gr = mkGraph (nub [(f i, a) | (i,a) <- labNodes ta_gr])
                    (nub [(f i , f j, b) | (i,j,b) <- labEdges ta_gr])
  , ta_starts = nub (f <$> ta_starts)
  , ta_flowEdges = nub (bimap f f <$> ta_flowEdges)
  }
