
module Failure where
import Control.Monad.Error (MonadError)
import qualified Data.Map as DM
import Errors (Error)
import Parser.Definition (runInteractiveParser)
import Parser.Types (typeSchemeP)
import Resolution.Definition (runResolverM)
import Resolution.Types (resolveTypeScheme)
import Syntax.Common.Polarity ( PolarityRep(PosRep), Polarity (Pos) )
import TypeAutomata.Simplify (simplify, printGraph)
import TypeAutomata.ToAutomaton (typeToAut)
import TypeAutomata.Minimize (minimize)
import TypeAutomata.RemoveAdmissible (removeAdmissableFlowEdges)
import TypeAutomata.Determinize (determinize)
import TypeAutomata.RemoveEpsilon (removeEpsilonEdges)
import TypeAutomata.Subsume (typeAutUnion, sucWith)
import TypeAutomata.Definition (TypeAut'(ta_core), ta_gr, TypeAutDet, TypeAutCore (ta_flowEdges), NodeLabel (nl_data), XtorLabel (labelName))
import Control.Monad.IO.Class ( MonadIO )
import Control.Monad (guard)
import Eval.Definition (runEval)
import Data.Graph.Inductive (lab)
import qualified Data.Set as S
import Data.Graph.Inductive.Graph (lsuc)

failEx :: (MonadError Error m, MonadIO m) => m (TypeAutDet 'Pos)
failEx = do
  ts  <- runInteractiveParser typeSchemeP "forall t0. { Ap(t0, return (rec r4.(t0 \\/ < Z, S( r4 ) >))) }"
  ts' <- runInteractiveParser typeSchemeP "{ Ap( (rec b.< Z , S( b ) >) , return (rec c.< Z , S( c ) >) ) }"
  let Right tsp  = runResolverM DM.empty (resolveTypeScheme PosRep ts)
  let Right tsp' = runResolverM DM.empty (resolveTypeScheme PosRep ts')
  tss  <- simplify tsp False ""
  tss' <- simplify tsp' False ""
  let Right aut0  = typeToAut tss
  let Right aut0' = typeToAut tss'
  let minAut  = minimize $ removeAdmissableFlowEdges $ determinize $ removeEpsilonEdges aut0
  let minAut' = minimize $ removeAdmissableFlowEdges $ determinize $ removeEpsilonEdges aut0'
  let unAut = typeAutUnion minAut minAut'
  let unDet = determinize unAut
  -- 0 is bottom left
  -- 2 is start
  -- 1 is middle right
  -- 3 is bottom right
  printGraph True True "unionGraph" unDet
  return unDet

-- parts of the subsumption pipeline that still work
--  failExWorks :: IO (TypeAutDet 'Pos)
failExWorks = do
  let i = 1
  let j = 0
  Right unDet <- runEval failEx mempty
  let unCore = ta_core unDet
  let flow = ta_flowEdges unCore
  guard (flow == [(i,j)])
  -- call to admissableM with unCore and an empty flowEdge list
  -- only use unGr, since flowEdge is empty
  let unGr = ta_gr unCore
  -- guard (e `elem` []) fails
  -- call to subTypeData
  let Just dat1 = let Just l = lab unGr i in nl_data l
  let Just dat2 = let Just l = lab unGr j in nl_data l
  -- we can ignore the "S.member" guard, since dat1 == dat2
  guard (dat1 == dat2)
  -- the first elem of lsuc fulfils xt==xt'
  let (n, el) = head $ lsuc unGr i
  guard $ n == 3
  let Just m = sucWith unGr j el
  guard $ m == 0
  return (n, m, unGr)

failExFails = do
  (i, j, unGr) <- failExWorks
  -- guard (e `elem` []) fails
  -- call to subTypeData
  let flow = (i, j)
  guard $ flow == (3,0)
  let Just dat1 = let Just l = lab unGr 3 in nl_data l
  let Just dat2 = let Just l = lab unGr 0 in nl_data l
  guard (dat1 == dat2)
  -- the first elem of lsuc fulfils xt==xt'
  let (n, el) = head $ lsuc unGr i
  guard $ n == 3
  guard $ n == i
  let Just m = sucWith unGr j el
  guard $ m == 0
  guard $ m == j
  putStrLn "Recursive loop with admissibleM aut (3,0)"
  return (n, m)
