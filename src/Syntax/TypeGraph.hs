module Syntax.TypeGraph where

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.PatriciaTree
import Data.Set (Set)

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

type TypeAut = (TypeGr, [Node], [FlowEdge])
