module TypeAutomata.RemoveAdmissible
  ( removeAdmissableFlowEdges
  ) where

import Syntax.CommonTerm (PrdCns(..))
import Syntax.Types
import Syntax.TypeAutomaton

import Data.Graph.Inductive.Graph

import Control.Applicative ((<|>))
import Control.Monad (guard, forM_)

import Data.List (delete)
import Data.Tuple (swap)
import Data.Maybe (isJust)
import qualified Data.Set as S

----------------------------------------------------------------------------------------
-- Removal of admissible flow edges.
--
-- The removal of admissible flow edges is part of the type simplification process.
-- In our representation of type automata, a type variable is represented by a flow edge
-- connecting two nodes. For example, "forall a. a -> a" is represented as
--
--            ----------------
--       -----| { Ap(_)[_] } |------
--       |    ----------------     |
--       |                         |
--       |Ap(1)                    |Ap[1]
--       |                         |
--   ----------        a       ----------
--   |        |~~~~~~~~~~~~~~~~|        |
--   ----------                ----------
--
--  But in some cases the flow edge is admissible. Consider the following automaton:
--
--            ----------------
--       -----| { Ap(_)[_] } |------
--       |    ----------------     |
--       |                         |
--       |Ap(1)                    |Ap[1]
--       |                         |
--   ----------        a       ----------
--   | Int    |~~~~~~~~~~~~~~~~|  Int   |
--   ----------                ----------
--
-- This automaton would be turned into the type "forall a. a /\ Int -> a \/ Int".
-- The admissibility check below recognizes that the flow edge "a" can be removed,
-- which results in the following automaton.
--
--            ----------------
--       -----| { Ap(_)[_] } |------
--       |    ----------------     |
--       |                         |
--       |Ap(1)                    |Ap[1]
--       |                         |
--   ----------                ----------
--   | Int    |                |  Int   |
--   ----------                ----------
--
-- This automaton is rendered as the (simpler) type "Int -> Int".
--
----------------------------------------------------------------------------------------

sucWith :: TypeGr -> Node -> EdgeLabelNormal -> Maybe Node
sucWith gr i el = lookup el (map swap (lsuc gr i))

subtypeData :: TypeAutDet pol -> FlowEdge -> Maybe ()
subtypeData aut@TypeAut{ ta_gr } (i,j) = do
  (HeadCons Neg (Just dat1) _ _) <- lab ta_gr i
  (HeadCons Pos (Just dat2) _ _) <- lab ta_gr j
  -- Check that all constructors in dat1 are also in dat2.
  forM_ (S.toList dat1) $ \xt -> guard (xt `S.member` dat2)
  -- Check arguments of each constructor of dat1.
  forM_ (labelName <$> S.toList dat1) $ \xt -> do
    forM_ [(n,el) | (n, el@(EdgeSymbol Data xt' Prd _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
      m <- sucWith ta_gr j el
      admissableM aut (n,m)
    forM_ [(n,el) | (n, el@(EdgeSymbol Data xt' Cns _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
      m <- sucWith ta_gr j el
      admissableM aut (m,n)

subtypeCodata :: TypeAutDet pol -> FlowEdge -> Maybe ()
subtypeCodata aut@TypeAut{ ta_gr } (i,j) = do
  (HeadCons Neg _ (Just codat1) _) <- lab ta_gr i
  (HeadCons Pos _ (Just codat2) _) <- lab ta_gr j
  -- Check that all destructors of codat2 are also in codat1.
  forM_ (S.toList codat2) $ \xt -> guard (xt `S.member` codat1)
  -- Check arguments of all destructors of codat2.
  forM_ (labelName <$> S.toList codat2) $ \xt -> do
    forM_ [(n,el) | (n, el@(EdgeSymbol Codata xt' Prd _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
      m <- sucWith ta_gr j el
      admissableM aut (m,n)
    forM_ [(n,el) | (n, el@(EdgeSymbol Codata xt' Cns _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
      m <- sucWith ta_gr j el
      admissableM aut (n,m)

subtypeNominal :: TypeAutDet pol -> FlowEdge -> Maybe ()
subtypeNominal TypeAut{ ta_gr } (i,j) = do
  (HeadCons Neg _ _ nominal1) <- lab ta_gr i
  (HeadCons Pos _ _ nominal2) <- lab ta_gr j
  guard $ not . S.null $ S.intersection nominal1 nominal2

admissableM :: TypeAutDet pol -> FlowEdge -> Maybe ()
admissableM aut@TypeAut{..} e =
      guard (e `elem` ta_flowEdges) <|>
      subtypeData aut e <|>
      subtypeCodata aut e <|>
      subtypeNominal aut e


-- this version of admissability check also accepts if the edge under consideration is in the set of known flow edges
-- needs to be seperated for technical reasons...
admissable :: TypeAutDet pol -> FlowEdge -> Bool
admissable aut@TypeAut {..} e = isJust $ admissableM (aut { ta_flowEdges = delete e ta_flowEdges }) e

removeAdmissableFlowEdges :: TypeAutDet pol -> TypeAutDet pol
removeAdmissableFlowEdges aut@TypeAut{..} = aut { ta_flowEdges = filter (not . admissable aut) ta_flowEdges }
