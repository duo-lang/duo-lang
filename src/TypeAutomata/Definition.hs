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

import Syntax.CST.Names ( XtorName )
import Syntax.CST.Types ( DataCodata(..), Arity, PrdCns(..))
import Syntax.RST.Types ( Polarity, PolarityRep(..))
import Syntax.RST.Names ( RnTypeName )
import Syntax.RST.Kinds
import Syntax.CST.Kinds ( Variance, PolyKind(..))

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

-- | A primitive type/calling convention
data PrimitiveType =
      I64 -- ^ Primitive signed 64-bit integer
    | F64 -- ^ Primitive double-precision floating point
    | PChar
    | PString
    deriving (Show, Eq, Ord)
    
data NodeLabel = 
  MkNodeLabel
    { nl_pol :: Polarity
    , nl_data :: Maybe (Set XtorLabel)
    , nl_codata :: Maybe (Set XtorLabel)
    -- Nominal type names with the arities of type parameters
    , nl_nominal :: Set (RnTypeName, [Variance])
    , nl_ref_data :: Map RnTypeName (Set XtorLabel)
    , nl_ref_codata :: Map RnTypeName (Set XtorLabel)
    , nl_kind :: PolyKind 
    }
  |
  MkPrimitiveNodeLabel
    { pl_pol :: Polarity
    , pl_prim :: PrimitiveType
    } deriving (Eq,Show,Ord)

emptyNodeLabel :: Polarity -> AnyKind -> NodeLabel
emptyNodeLabel _ (MkPknd (KindVar _)) = error "at this point no KindVars should be in the program"
emptyNodeLabel pol (MkPknd pk)  = MkNodeLabel pol Nothing Nothing S.empty M.empty M.empty pk
emptyNodeLabel pol MkI64        = MkPrimitiveNodeLabel pol I64
emptyNodeLabel pol MkF64        = MkPrimitiveNodeLabel pol F64
emptyNodeLabel pol MkString     = MkPrimitiveNodeLabel pol PString
emptyNodeLabel pol MkChar       = MkPrimitiveNodeLabel pol PChar

singleNodeLabelNominal :: Polarity -> (RnTypeName, [Variance]) ->  PolyKind -> NodeLabel
singleNodeLabelNominal pol nominal k = MkNodeLabel { nl_pol = pol, nl_data = Nothing, nl_codata = Nothing, nl_nominal = S.singleton nominal, nl_ref_data = M.empty, nl_ref_codata = M.empty, nl_kind = k }

singleNodeLabelXtor :: Polarity -> DataCodata -> Maybe RnTypeName -> Set XtorLabel -> PolyKind -> NodeLabel
singleNodeLabelXtor pol Data   Nothing   xtors k = MkNodeLabel { nl_pol = pol, nl_data = Just xtors, nl_codata = Nothing,    nl_nominal = S.empty, nl_ref_data = M.empty,              nl_ref_codata = M.empty,         nl_kind = k }
singleNodeLabelXtor pol Codata Nothing   xtors k = MkNodeLabel { nl_pol = pol, nl_data = Nothing,    nl_codata = Just xtors, nl_nominal = S.empty, nl_ref_data = M.empty,              nl_ref_codata = M.empty,         nl_kind = k }
singleNodeLabelXtor pol Data   (Just tn) xtors k = MkNodeLabel { nl_pol = pol, nl_data = Nothing,    nl_codata = Nothing,    nl_nominal = S.empty, nl_ref_data = M.singleton tn xtors, nl_ref_codata = M.empty,         nl_kind = k }
singleNodeLabelXtor pol Codata (Just tn) xtors k = MkNodeLabel { nl_pol = pol, nl_data = Nothing,    nl_codata = Nothing,    nl_nominal = S.empty, nl_ref_data = M.empty,              nl_ref_codata = M.singleton tn xtors, nl_kind = k }

getPolarityNL :: NodeLabel -> Polarity
getPolarityNL (MkNodeLabel pol _ _ _ _ _ _) = pol
getPolarityNL (MkPrimitiveNodeLabel pol _) = pol

getKindNL :: NodeLabel -> PolyKind 
getKindNL (MkNodeLabel _ _ _ _ _ _ (KindVar _)) = error "at this point no KindVars should be in the program"
getKindNL (MkNodeLabel _ _ _ _ _ _ pk) = pk
getKindNL (MkPrimitiveNodeLabel _ _) = error "can't get polykind of primitive type"
--getKindNL (MkPrimitiveNodeLabel _ I64) = I64Rep
--getKindNL (MkPrimitiveNodeLabel _ F64) = F64Rep
--getKindNL (MkPrimitiveNodeLabel _ PChar) = CharRep
--getKindNL (MkPrimitiveNodeLabel _ PString) = StringRep
      
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
mapTypeAutCore f aut = TypeAutCore
  { ta_gr = mkGraph (nub [(f i, a) | (i,a) <- labNodes aut.ta_gr])
            (nub [(f i , f j, b) | (i,j,b) <- labEdges aut.ta_gr])
  , ta_flowEdges = nub (bimap f f <$> aut.ta_flowEdges)
  }

-- Maps a function on nodes over a type automaton
mapTypeAut :: (Ord a, Functor f, Nubable f) => (Node -> Node) -> TypeAut' a f pol -> TypeAut' a f pol
mapTypeAut f aut = TypeAut
  { ta_pol = aut.ta_pol
  , ta_starts = nub (f <$> aut.ta_starts)
  , ta_core = mapTypeAutCore f aut.ta_core
  }

removeRedundantEdges :: TypeGr -> TypeGr
removeRedundantEdges = gmap (\(ins,i,l,outs) -> (nub ins, i, l, nub outs))

removeRedundantEdgesCore :: TypeAutCore EdgeLabelNormal -> TypeAutCore EdgeLabelNormal
removeRedundantEdgesCore aut = aut { ta_gr = removeRedundantEdges aut.ta_gr }

removeRedundantEdgesAut :: TypeAutDet pol -> TypeAutDet pol
removeRedundantEdgesAut aut = aut { ta_core = removeRedundantEdgesCore aut.ta_core }

delAllLEdges :: Eq b => [LEdge b] -> Gr NodeLabel b -> Gr NodeLabel b
delAllLEdges es gr = foldr delAllLEdge gr es
