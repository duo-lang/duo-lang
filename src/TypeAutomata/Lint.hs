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
import qualified Data.Set
import Syntax.CommonTerm (XtorName)


-- | Check the invariants of the type automaton.
lint :: TypeAut' (EdgeLabel a) f pol  -> Either Error ()
lint aut = do
  lintFlowEdges aut
  lintEpsilonEdges aut
  lintSymbolEdges aut
  lintStructuralNodes aut


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

-- | Check that every structural Xtor has at least one outgoing Symbol Edge for every argument of the Xtor.
lintStructuralNodes :: TypeAut' (EdgeLabel a) f pol -> Either Error ()
lintStructuralNodes TypeAut { ta_core = TypeAutCore { ta_gr }} = forM_ (labNodes ta_gr) (lintStructuralNode ta_gr)

-- | Collect all the xtors labels of a node and check them.
lintStructuralNode :: Gr NodeLabel (EdgeLabel a) -> LNode NodeLabel -> Either Error ()
lintStructuralNode gr (n, nl) = do
  let toList = maybe [] Data.Set.toList
  let xtors = toList (nl_data nl) ++ toList (nl_codata nl)
  forM_ xtors (lintXtor gr n)

-- | Check whether all fields of the Xtor Label have at least one outgoing edge starting from the node.
lintXtor :: Gr NodeLabel (EdgeLabel a) -> Node -> XtorLabel -> Either Error ()
lintXtor gr n (MkXtorLabel xn prdIdx cnsIdx) = do
  let outs = (\(_,_,x) -> x) <$> out gr n
  -- Check Prd arguments
  forM_ [0..(prdIdx - 1)] (lintXtorArgument outs xn Prd)
  -- Check Cns arguments
  forM_ [0..(cnsIdx - 1)] (lintXtorArgument outs xn Cns)

lintXtorArgument :: [EdgeLabel a] -> XtorName -> PrdCns -> Int -> Either Error ()
lintXtorArgument outs xn pc i = do
  let filtered = [ () | EdgeSymbol _ xn' pc' i' <- outs, xn == xn', pc == pc', i == i']
  if null filtered
    then Left (TypeAutomatonError ("TypeAutomata Linter: The Xtor " <> T.pack (show xn) <> " has missing outgoing edge"))
    else pure ()
