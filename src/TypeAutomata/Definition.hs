module TypeAutomata.Definition where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Set (Set)
import Data.Set qualified as S
import Data.Map (Map)
import Data.Map qualified as M
import Data.Bifunctor (bimap)
import Data.Functor.Identity
import Data.Containers.ListUtils (nubOrd)
import Data.Void

import Syntax.Common.Names ( RnTypeName, XtorName )
import Syntax.Common.PrdCns ( Arity, PrdCns )
import Syntax.Common.XData ( DataCodata(..) )
import Syntax.Common.Polarity ( Polarity, PolarityRep )
import Syntax.Common.Primitives ( PrimitiveType )
import Syntax.Common.Kinds ( Variance )

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
-- A nominal type is represented as a node with the `nl_nominal` field set to the
-- name of the nominal type:
--
--    ------------------------
--    |                      |
--    | nl_nominal = { Nat } |    =   Nat
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
--    |                                        |     Cons(1)    |         |
--    | nl_data =  { Nil(0)[0], Cons(2)[0] }   |--------------->|   ty    |
--    |                                        |                |         |
--    |----------------------------------------|                |---------|
--           |                      /\
--           |                       |
--           -------------------------
--                    Cons(2)
--
--                    = mu r. < Nil , Cons(ty,r) >
--
-- ## Union and Intersection Types:
--
-- Unions and intersections are recorded within a same node label. Whether a node
-- is interpreted as a union or intersection depends on it's polarity. E.g.:
--
--
--    ------------------------------
--    |                            |
--    | nl_polarity = Pos          |
--    | nl_nominal = { Nat, Bool } |    =   Nat \/ Bool
--    |                            |
--    ------------------------------
--
--    ------------------------------
--    |                            |
--    | nl_polarity = Neg          |
--    | nl_nominal = { Nat, Bool } |    =   Nat /\ Bool
--    |                            |
--    ------------------------------
--
-- ## Refinement Types:
--
-- Refinement types are represented by the `nl_ref_data` and `nl_ref_codata` node
-- labels. These map type names to their corresponding set of xtor labels.
--
--               ------------------------------------
--               |                                  |
--               | nl_polarity = Pos                |
--               | nl_ref_data = [ Bool -> { True } |
--               |               , Nat  -> { Z } ]  |
--               |                                  |
--               ------------------------------------
--
--       = < Nat | S(...) > \/ < Bool | True >
--
-- ## Type variables
--
-- Type variables are represented by flow-edges, which always connect a
-- positive and a negative node. Flow edges are drawn as squiggly lines.
--
--                 ---------------------------------
--                 |                               |
--            -----|    nl_codata = { Ap(1)[1] }   |-----
--            |    |                               |    |
--            |    ---------------------------------    |
--     Ap(1)  |                                         | Ap[1]
--            |                                         |
--     ---------------------        a         ---------------------
--     | nl_Polarity = Neg |~~~~~~~~~~~~~~~~~~| nl_polarity = Pos |
--     ---------------------                  ---------------------
--
--                       = forall a. { Ap(a)[a] }
--
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Node labels for type automata
--------------------------------------------------------------------------------

data XtorLabel = MkXtorLabel
  { labelName :: XtorName
  , labelArity :: Arity
  }
  deriving (Eq, Show, Ord)

data NodeLabel = 
  MkNodeLabel
    { nl_pol :: Polarity
    , nl_data :: Maybe (Set XtorLabel)
    , nl_codata :: Maybe (Set XtorLabel)
    -- Nominal type names with the arities of type parameters
    , nl_nominal :: Set (RnTypeName, [Variance])
    , nl_ref_data :: Map RnTypeName (Set XtorLabel)
    , nl_ref_codata :: Map RnTypeName (Set XtorLabel)
    }
  |
  MkPrimitiveNodeLabel
    { pl_pol :: Polarity
    , pl_prim :: PrimitiveType
    } deriving (Eq,Show,Ord)

emptyNodeLabel :: Polarity -> NodeLabel
emptyNodeLabel pol = MkNodeLabel pol Nothing Nothing S.empty M.empty M.empty

-- emptyPrimNodeLabel :: Polarity -> NodeLabel
-- emptyPrimNodeLabel pol = MkPrimitiveNodeLabel pol S.empty

singleNodeLabel :: Polarity -> DataCodata -> Maybe RnTypeName -> Set XtorLabel -> NodeLabel
singleNodeLabel pol Data Nothing xtors   = MkNodeLabel pol (Just xtors) Nothing S.empty M.empty M.empty
singleNodeLabel pol Codata Nothing xtors = MkNodeLabel pol Nothing (Just xtors) S.empty M.empty M.empty
singleNodeLabel pol Data (Just tn) xtors   = MkNodeLabel pol Nothing Nothing S.empty (M.singleton tn xtors) M.empty
singleNodeLabel pol Codata (Just tn) xtors = MkNodeLabel pol Nothing Nothing S.empty M.empty (M.singleton tn xtors)

getPolarityNL :: NodeLabel -> Polarity
getPolarityNL (MkNodeLabel pol _ _ _ _ _) = pol
getPolarityNL (MkPrimitiveNodeLabel pol _) = pol

--------------------------------------------------------------------------------
-- Edge labels for type automata
--------------------------------------------------------------------------------

data EdgeLabel a
  = EdgeSymbol DataCodata XtorName PrdCns Int
  | EpsilonEdge a
  | RefineEdge RnTypeName
  | TypeArgEdge RnTypeName Variance Int
  deriving (Eq, Show, Ord)

type EdgeLabelNormal  = EdgeLabel Void
type EdgeLabelEpsilon = EdgeLabel ()

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

--------------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------------

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

removeRedundantEdges :: TypeGr -> TypeGr
removeRedundantEdges = gmap (\(ins,i,l,outs) -> (nub ins, i, l, nub outs))

removeRedundantEdgesCore :: TypeAutCore EdgeLabelNormal -> TypeAutCore EdgeLabelNormal
removeRedundantEdgesCore aut@TypeAutCore{..} = aut { ta_gr = removeRedundantEdges ta_gr }

removeRedundantEdgesAut :: TypeAutDet pol -> TypeAutDet pol
removeRedundantEdgesAut aut@TypeAut { ta_core } = aut { ta_core = removeRedundantEdgesCore ta_core }

delAllLEdges :: Eq b => [LEdge b] -> Gr NodeLabel b -> Gr NodeLabel b
delAllLEdges es gr = foldr delAllLEdge gr es
