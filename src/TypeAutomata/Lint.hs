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


-- | Check the invariants of the type automaton.
lint :: TypeAut' a f pol  -> Either Error ()
lint aut = do
  lintFlowEdges aut


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
    leftLabel <- getNodeLabel ta_gr left
    rightLabel <- getNodeLabel ta_gr right
    case nl_pol leftLabel of
      Pos -> Left (TypeAutomatonError "TypeAutomata Linter: Left endpoint of flowedge is positive")
      Neg -> pure ()
    case nl_pol rightLabel of
      Pos -> pure ()
      Neg -> Left (TypeAutomatonError "TypeAutomata Linter: Right endpoint of flowedge is negative")

