module TypeAutomata.Lint
  ( lint
  ) where

import Syntax.Types
import Errors
import TypeAutomata.Definition
import Control.Monad (forM_)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive (Gr)
import qualified Data.Text as T
import Syntax.STerms (PrdCns(..))


-- | Check the invariants of the type automaton.
lint :: TypeAut' (EdgeLabel a) f pol  -> Either Error ()
lint aut = do
  lintFlowEdges aut
  lintEpsilonEdges aut
  lintSymbolEdges aut


getNodeLabel :: Gr NodeLabel a -> Node -> Either Error NodeLabel
getNodeLabel gr n = case lab gr n of
  Nothing -> Left (TypeAutomatonError $ "TypeAutomata Linter: The node " <> T.pack (show n) <> " is not contained in graph")
  Just label -> pure label

-- | Check for every flow edge of a type automaton that:
-- 1.) Both nodes are contained in the corresponding graph.
-- 2.) The left node of the flowedge is negative and the right node is positive.
lintFlowEdges :: TypeAut' a f pol  -> Either Error ()
lintFlowEdges TypeAut { ta_core = TypeAutCore { ta_gr, ta_flowEdges } } = do
  forM_ ta_flowEdges $ \(left,right) -> do
    leftPol <- nl_pol <$> getNodeLabel ta_gr left
    rightPol <- nl_pol <$> getNodeLabel ta_gr right
    case leftPol of
      Pos -> Left (TypeAutomatonError "TypeAutomata Linter: Left endpoint of flowedge is positive")
      Neg -> pure ()
    case rightPol of
      Pos -> pure ()
      Neg -> Left (TypeAutomatonError "TypeAutomata Linter: Right endpoint of flowedge is negative")


-- | Check that epsilon edges connect nodes of the same polarity.
lintEpsilonEdges :: TypeAut' (EdgeLabel a) f pol -> Either Error ()
lintEpsilonEdges TypeAut { ta_core = TypeAutCore { ta_gr }} = do
  let edges = [(i,j) | (i,j,EpsilonEdge _) <- labEdges ta_gr]
  forM_ edges $ \(i,j) -> do
    iPolarity <- nl_pol <$> getNodeLabel ta_gr i
    jPolarity <- nl_pol <$> getNodeLabel ta_gr j
    if iPolarity /= jPolarity
      then Left (TypeAutomatonError "TypeAutomata Linter: Epsilon Edge connects nodes with different polarity.")
      else pure ()

-- | Check that symbol edges connect nodes of the correct polarity.
lintSymbolEdges :: TypeAut' (EdgeLabel a) f pol -> Either Error ()
lintSymbolEdges TypeAut { ta_core = TypeAutCore { ta_gr }} = do
  let edges = [(i,j,dataCodata,prdCns) | (i,j,EdgeSymbol dataCodata _ prdCns _) <- labEdges ta_gr]
  forM_ edges $ \(i,j, dataCodata, prdCns) -> do
    iPolarity <- nl_pol <$> getNodeLabel ta_gr i
    jPolarity <- nl_pol <$> getNodeLabel ta_gr j
    let err = TypeAutomatonError "TypeAutomata Linter: Incorrect Symbol Edge"
    case (dataCodata, prdCns) of
      (Data, Prd)   -> if iPolarity == jPolarity then pure () else Left err
      (Data, Cns)   -> if iPolarity /= jPolarity then pure () else Left err
      (Codata, Prd) -> if iPolarity /= jPolarity then pure () else Left err
      (Codata, Cns) -> if iPolarity == jPolarity then pure () else Left err
