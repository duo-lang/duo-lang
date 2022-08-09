module TypeAutomata.Lint
  ( lint
  ) where

import Control.Monad (forM_)
import Control.Monad.Except (MonadError)
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive (Gr)
import Data.List.NonEmpty (NonEmpty)
import Data.Set qualified as S
import Data.Text qualified as T

import Errors
import Syntax.Common.Polarity
import Syntax.Common.PrdCns
import Syntax.CST.Types
import Syntax.Common.Names
import TypeAutomata.Definition
import Utils ( defaultLoc, enumerate )

-- | Check the invariants of the type automaton.
lint :: MonadError (NonEmpty Error) m
     => TypeAut' (EdgeLabel a) f pol
     -> m ()
lint aut = do
  lintFlowEdges aut
  lintEpsilonEdges aut
  lintSymbolEdges aut
  lintStructuralNodes aut


getNodeLabel :: MonadError (NonEmpty Error) m
             => Gr NodeLabel a -> Node -> m NodeLabel
getNodeLabel gr n = case lab gr n of
  Nothing -> throwAutomatonError defaultLoc ["TypeAutomata Linter: The node " <> T.pack (show n) <> " is not contained in graph"]
  Just label -> pure label

-- | Check for every flow edge of a type automaton that:
-- 1.) Both nodes are contained in the corresponding graph.
-- 2.) The left node of the flowedge is negative and the right node is positive.
lintFlowEdges :: MonadError (NonEmpty Error) m
              => TypeAut' a f pol  -> m ()
lintFlowEdges TypeAut { ta_core = TypeAutCore { ta_gr, ta_flowEdges } } = do
  forM_ ta_flowEdges $ \(left,right) -> do
    leftPol <- getPolarityNL <$> getNodeLabel ta_gr left
    rightPol <- getPolarityNL <$> getNodeLabel ta_gr right
    case leftPol of
      Pos -> throwAutomatonError defaultLoc ["TypeAutomata Linter: Left endpoint of flowedge is positive"]
      Neg -> pure ()
    case rightPol of
      Pos -> pure ()
      Neg -> throwAutomatonError defaultLoc ["TypeAutomata Linter: Right endpoint of flowedge is negative"]


-- | Check that epsilon edges connect nodes of the same polarity.
lintEpsilonEdges :: MonadError (NonEmpty Error) m
                 => TypeAut' (EdgeLabel a) f pol -> m ()
lintEpsilonEdges TypeAut { ta_core = TypeAutCore { ta_gr }} = do
  let edges = [(i,j) | (i,j,EpsilonEdge _) <- labEdges ta_gr]
  forM_ edges $ \(i,j) -> do
    iPolarity <- getPolarityNL <$> getNodeLabel ta_gr i
    jPolarity <- getPolarityNL <$> getNodeLabel ta_gr j
    if iPolarity /= jPolarity
      then throwAutomatonError defaultLoc ["TypeAutomata Linter: Epsilon Edge connects nodes with different polarity."]
      else pure ()

-- | Check that symbol edges connect nodes of the correct polarity.
lintSymbolEdges :: MonadError (NonEmpty Error) m
                => TypeAut' (EdgeLabel a) f pol -> m ()
lintSymbolEdges TypeAut { ta_core = TypeAutCore { ta_gr }} = do
  let edges = [(i,j,dataCodata,prdCns) | (i,j,EdgeSymbol dataCodata _ prdCns _) <- labEdges ta_gr]
  forM_ edges $ \(i,j, dataCodata, prdCns) -> do
    iPolarity <- getPolarityNL <$> getNodeLabel ta_gr i
    jPolarity <- getPolarityNL <$> getNodeLabel ta_gr j
    let err = "TypeAutomata Linter: Incorrect Symbol Edge"
    case (dataCodata, prdCns) of
      (Data, Prd)   -> if iPolarity == jPolarity then pure () else throwAutomatonError defaultLoc [err]
      (Data, Cns)   -> if iPolarity /= jPolarity then pure () else throwAutomatonError defaultLoc [err]
      (Codata, Prd) -> if iPolarity /= jPolarity then pure () else throwAutomatonError defaultLoc [err]
      (Codata, Cns) -> if iPolarity == jPolarity then pure () else throwAutomatonError defaultLoc [err]

-- | Check that every structural Xtor has at least one outgoing Symbol Edge for every argument of the Xtor.
lintStructuralNodes :: MonadError (NonEmpty Error) m
                    => TypeAut' (EdgeLabel a) f pol -> m ()
lintStructuralNodes TypeAut { ta_core = TypeAutCore { ta_gr }} = forM_ (labNodes ta_gr) (lintStructuralNode ta_gr)

-- | Collect all the xtors labels of a node and check them.
lintStructuralNode :: MonadError (NonEmpty Error) m
                   => Gr NodeLabel (EdgeLabel a) -> LNode NodeLabel -> m ()
lintStructuralNode _ (_, MkPrimitiveNodeLabel{}) = pure ()
lintStructuralNode gr (n, nl) = do
  let toList = maybe [] S.toList
  let xtors = toList (nl_data nl) ++ toList (nl_codata nl)
  forM_ xtors (lintXtor gr n)

-- | Check whether all fields of the Xtor Label have at least one outgoing edge starting from the node.
lintXtor :: MonadError (NonEmpty Error) m
         => Gr NodeLabel (EdgeLabel a) -> Node -> XtorLabel -> m ()
lintXtor gr n (MkXtorLabel xn arity) = do
  let outs = (\(_,_,x) -> x) <$> out gr n
  forM_ (enumerate arity) $ \(n,pc) -> lintXtorArgument outs xn pc n

lintXtorArgument :: MonadError (NonEmpty Error) m
                 => [EdgeLabel a] -> XtorName -> PrdCns -> Int -> m ()
lintXtorArgument outs xn pc i = do
  let filtered = [ () | EdgeSymbol _ xn' pc' i' <- outs, xn == xn', pc == pc', i == i']
  if null filtered
    then throwAutomatonError defaultLoc ["TypeAutomata Linter: The Xtor " <> T.pack (show xn) <> " has missing outgoing edge"]
    else pure ()
