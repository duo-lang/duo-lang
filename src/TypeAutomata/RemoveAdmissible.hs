module TypeAutomata.RemoveAdmissible
  ( removeAdmissableFlowEdges
  ) where

import Syntax.CommonTerm (PrdCns(..))
import Syntax.Types
import Syntax.TypeAutomaton

import Data.Graph.Inductive.Graph

import Control.Applicative ((<|>))
import Control.Monad.State

import Data.List (delete)
import Data.Tuple (swap)
import Data.Maybe (isJust)
import qualified Data.Set as S

----------------------------------------------------------------------------------------
-- Flow edge admissability check
----------------------------------------------------------------------------------------

sucWith :: (DynGraph gr, Eq b) => gr a b -> Node -> b -> Maybe Node
sucWith gr i el = lookup el (map swap (lsuc gr i))

-- this version of admissability check also accepts if the edge under consideration is in the set of known flow edges
-- needs to be seperated for technical reasons...
admissable :: TypeAutDet pol -> FlowEdge -> Bool
admissable aut@TypeAut {..} e = isJust $ admissableM (aut { ta_flowEdges = delete e ta_flowEdges }) e

admissableM :: TypeAutDet pol -> FlowEdge -> Maybe ()
admissableM aut@TypeAut{..} e@(i,j) =
    let
      subtypeData = do -- Maybe monad
        (HeadCons Neg (Just dat1) _ _) <- lab ta_gr i
        (HeadCons Pos (Just dat2) _ _) <- lab ta_gr j
        _ <- forM (labelName <$> S.toList dat1) $ \xt -> guard (xt `S.member` (labelName `S.map` dat2))
        _ <- forM (labelName <$> S.toList dat1) $ \xt -> do
          _ <- forM [(n,el) | (n, el@(EdgeSymbol Data xt' Prd _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
            m <- sucWith ta_gr j el
            admissableM aut (n,m)
          _ <- forM [(n,el) | (n, el@(EdgeSymbol Data xt' Cns _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
            m <- sucWith ta_gr j el
            admissableM aut (m,n)
          return ()
        return ()
      subtypeCodata = do -- Maybe monad
        (HeadCons Neg _ (Just codat1) _) <- lab ta_gr i
        (HeadCons Pos _ (Just codat2) _) <- lab ta_gr j
        _ <- forM (labelName <$> S.toList codat2) $ \xt -> guard (xt `S.member` (labelName `S.map` codat1))
        _ <- forM (labelName <$> S.toList codat2) $ \xt -> do
          _ <- forM [(n,el) | (n, el@(EdgeSymbol Data xt' Prd _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
            m <- sucWith ta_gr j el
            admissableM aut (m,n)
          _ <- forM [(n,el) | (n, el@(EdgeSymbol Data xt' Cns _)) <- lsuc ta_gr i, xt == xt'] $ \(n,el) -> do
            m <- sucWith ta_gr j el
            admissableM aut (n,m)
          return ()
        return ()
      subTypeNominal = do -- Maybe monad
        (HeadCons Neg _ _ nominal1) <- lab ta_gr i
        (HeadCons Pos _ _ nominal2) <- lab ta_gr j
        guard $ not . S.null $ S.intersection nominal1 nominal2
    in
      guard (e `elem` ta_flowEdges) <|> subtypeData <|> subtypeCodata <|> subTypeNominal


removeAdmissableFlowEdges :: TypeAutDet pol -> TypeAutDet pol
removeAdmissableFlowEdges aut@TypeAut{..} = aut { ta_flowEdges = filter (not . admissable aut) ta_flowEdges }
