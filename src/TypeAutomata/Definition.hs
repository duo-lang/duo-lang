module TypeAutomata.Definition where

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

--------------------------------------------------------------------------------
-- # Type Automata
--
-- Type automata are an alternative representation of types, that is, there is a
-- 1:1 correspondence between (syntactic) types and type automata, which is witnessed by
-- the two functions  `fromAutomaton` and `toAutomaton` (not defined in this module).
--
--                    toAutomaton
--        Typ pol <----------------> TypeAut pol
--                   fromAutomaton
--
-- The reason for representing types as automata is that the automata representation
-- allows to define type simplification as a standard simplification algorithm on
-- DFAs/NFAs. A type automaton is represented as a graph with some extra structure
-- on top.
--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- # Representation of Types
--
-- Types are represented as a combination of node labels and node edges:
--
-- ## Nominal Types:
--
-- A nominal type is represented as a node with the `hc_nominal` field set to the
-- name of the nominal type:
--
--    ------------------------
--    |                      |
--    | hc_nominal = { Nat } |    =   Nat
--    |                      |
--    ------------------------
--
-- ## Recursive Types:
--
-- Recursive types are represented as a cycle in the type graph:
--
--    ------
--    |    |
--    | ty | -----|
--    |    |      |               = mu alpha. ty
--    ------      |
--      /\        |
--       |        |
--       ----------
--
-- ## Structural Types:
--
-- Let's consider the encoding of structural data types. A list of `ty` is
-- represented as the following graph. At the node we record the names of the
-- constructors (or destructors) of the type, together with their arity.
-- The types of the producer and consumer arguments of the xtors are recorded
-- as edges to other nodes which encode those argument types.
--
--
--    |----------------------------------------|                |---------|
--    |                                        |    Cons(1)     |         |
--    | hc_data =  { 'Nil(0)[0], 'Cons(2)[0] } |--------------->|   ty    |
--    |                                        |                |         |
--    |----------------------------------------|                |---------|
--           |                      /\
--           |                       |
--           -------------------------
--                   Cons(2)
--
--                    = mu r. < Nil | Cons(ty,r) >
--
--
-- ## Union and Intersection Types:
--
-- Unions and intersections are recorded within a same node label. Whether a node
-- is interpreted as a union or intersection depends on it's polarity. E.g.:
--
--
--    ------------------------------
--    |                            |
--    | hc_polarity = Pos          |
--    | hc_nominal = { Nat, Bool } |    =   Nat \/ Bool
--    |                            |
--    ------------------------------
--
--    ------------------------------
--    |                            |
--    | hc_polarity = Neg          |
--    | hc_nominal = { Nat, Bool } |    =   Nat /\ Bool
--    |                            |
--    ------------------------------
--
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Node labels for type automata
--------------------------------------------------------------------------------

data XtorLabel = MkXtorLabel
  { labelName :: XtorName
  , labelPrdArity :: Int
  , labelCnsArity :: Int
  }
  deriving (Eq, Show, Ord)

data NodeLabel = MkNodeLabel
  { nl_pol :: Polarity
  , nl_data :: Maybe (Set XtorLabel)
  , nl_codata :: Maybe (Set XtorLabel)
  , nl_nominal :: Set TypeName
  } deriving (Eq,Show,Ord)

emptyNodeLabel :: Polarity -> NodeLabel
emptyNodeLabel pol = MkNodeLabel pol Nothing Nothing S.empty

singleNodeLabel :: Polarity -> DataCodata -> Set XtorLabel -> NodeLabel
singleNodeLabel pol Data xtors   = MkNodeLabel pol (Just xtors) Nothing S.empty
singleNodeLabel pol Codata xtors = MkNodeLabel pol Nothing (Just xtors) S.empty

--------------------------------------------------------------------------------
-- Edge labels for type automata
--------------------------------------------------------------------------------

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

--------------------------------------------------------------------------------
-- Flow edges
--------------------------------------------------------------------------------

type FlowEdge = (Node, Node)

--------------------------------------------------------------------------------
-- Type Automata
--------------------------------------------------------------------------------

data TypeAutCore a = TypeAutCore
  { ta_gr :: Gr NodeLabel a
  , ta_flowEdges :: [FlowEdge]
  }
deriving instance Show (TypeAutCore EdgeLabelNormal)
deriving instance Show (TypeAutCore EdgeLabelEpsilon)

type TypeGr = Gr NodeLabel EdgeLabelNormal
type TypeGrEps = Gr NodeLabel EdgeLabelEpsilon

data TypeAut' a f (pol :: Polarity) = TypeAut
  { ta_pol :: PolarityRep pol
  , ta_starts :: f Node
  , ta_core :: TypeAutCore a
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


mapTypeAutCore :: Ord a => (Node -> Node) -> TypeAutCore a -> TypeAutCore a
mapTypeAutCore f TypeAutCore { ta_gr, ta_flowEdges } = TypeAutCore
  { ta_gr = mkGraph (nub [(f i, a) | (i,a) <- labNodes ta_gr])
            (nub [(f i , f j, b) | (i,j,b) <- labEdges ta_gr])
  , ta_flowEdges = nub (bimap f f <$> ta_flowEdges)
  }

-- Maps a function on nodes over a type automaton
mapTypeAut :: (Ord a, Functor f, Nubable f) => (Node -> Node) -> TypeAut' a f pol -> TypeAut' a f pol
mapTypeAut f TypeAut { ta_pol, ta_starts, ta_core } = TypeAut
  { ta_pol = ta_pol
  , ta_starts = nub (f <$> ta_starts)
  , ta_core = mapTypeAutCore f ta_core
  }
