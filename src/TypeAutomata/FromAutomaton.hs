module TypeAutomata.FromAutomaton ( autToType ) where

import Syntax.Terms
import Syntax.Types
import Syntax.TypeGraph
import Utils
import TypeAutomata.FlowAnalysis

import Control.Monad.Reader
import Data.Maybe (fromJust)

import Data.List (sortBy, groupBy)
import Data.Functor.Identity
import Data.Set (Set)
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS (dfs)

--------------------------------------------------------------------------
-- Type automata -> Target types
--------------------------------------------------------------------------

data AutToTypeState = AutToTypeState { tvMap :: Map Node (Set TVar)
                                     , graph :: TypeGr
                                     , cache :: Set Node
                                     }

type AutToTypeM a = Reader AutToTypeState a

autToType :: TypeAutDet -> TypeScheme
autToType aut@TypeAut{..} =
  let
    mp = getFlowAnalysisMap aut
    startState = AutToTypeState mp ta_gr S.empty
    monotype = runReader (nodeToType (runIdentity ta_starts)) startState
    tvars = S.toList $ S.unions (M.elems mp)
  in
    TypeScheme tvars monotype

visitNode :: Node -> AutToTypeState -> AutToTypeState
visitNode i aut@AutToTypeState { graph, cache } =
  aut { graph = delEdges [(i,n) | n <- suc graph i, i `elem` dfs [n] graph] graph
      , cache = S.insert i cache }

checkCache :: Node -> AutToTypeM Bool
checkCache i = do
  cache <- asks cache
  return (i `S.member` cache)

nodeToTVars :: Node -> AutToTypeM [TargetType]
nodeToTVars i = do
  tvMap <- asks tvMap
  return (TTyTVar <$> (S.toList $ fromJust $ M.lookup i tvMap))

nodeToOuts :: Node -> AutToTypeM [(EdgeLabel, Node)]
nodeToOuts i = do
  gr <- asks graph
  let (_,_,_,outs) = context gr i
  return outs

filterSortOuts :: [(EdgeLabel, Node)] -> DataCodata -> XtorName -> PrdCns -> [[Node]]
filterSortOuts outs dc xt pc =
  let
    filtereds = [ (el, n) | (el@(EdgeSymbol dc' xt' pc' _), n) <- outs, dc == dc', xt == xt', pc == pc' ]
    sortFun (EdgeSymbol _ _ _ j1,_) (EdgeSymbol _ _ _ j2,_) = j1 `compare` j2
    sorteds = sortBy sortFun filtereds
    groupFun (EdgeSymbol _ _ _ j1,_) (EdgeSymbol _ _ _ j2,_) = j1 == j2
    groupeds = groupBy groupFun sorteds
  in
    (fmap . fmap) snd $ groupeds

bar :: [[Node]] -> DataCodata -> PrdCns -> Polarity -> AutToTypeM [TargetType]
bar nodes dc pc pol = do
  forM nodes $ \ns -> do
    typs <- forM ns $ \n -> do
      nodeToType n
    return $ unionOrInter (applyVariance dc pc pol) typs

nodeToType :: Node -> AutToTypeM TargetType
nodeToType i = do
  -- First we check if i is in the cache.
  -- If i is in the cache, we return a recursive variable.
  inCache <- checkCache i
  case inCache of
    True -> return $ TTyRVar (MkRVar ("r" ++ show i))
    False -> do
      outs <- nodeToOuts i
      gr <- asks graph
      let (_,_,(pol,HeadCons datSet codatSet),_) = context gr i
      let (maybeDat,maybeCodat) = (S.toList <$> datSet, S.toList <$> codatSet)
      resType <- local (visitNode i) $ do
        -- Creating type variables
        varL <- nodeToTVars i
        -- Creating data types
        datL <- case maybeDat of
          {Nothing -> return [] ;
          Just xtors -> do
            sig <- forM xtors $ \xt -> do
              let prdNodes = filterSortOuts outs Data xt Prd
              prdTypes <- bar prdNodes Data Prd pol
              let cnsNodes = filterSortOuts outs Data xt Cns
              cnsTypes <- bar cnsNodes Data Cns pol
              return (MkXtorSig xt (Twice prdTypes cnsTypes))
            return [TTySimple Data sig]}
        -- Creating codata types
        codatL <- case maybeCodat of
          {Nothing -> return [] ;
          Just xtors -> do
            sig <- forM xtors $ \xt -> do
              let prdNodes = filterSortOuts outs Codata xt Prd
              prdTypes <- bar prdNodes Codata Prd pol
              let cnsNodes = filterSortOuts outs Codata xt Cns
              cnsTypes <- bar cnsNodes Codata Cns pol
              return (MkXtorSig xt (Twice prdTypes cnsTypes))
            return [TTySimple Codata sig]}
        return $ unionOrInter pol (varL ++ datL ++ codatL)

      -- If the graph is cyclic, make a recursive type
      if i `elem` dfs (suc gr i) gr
        then return $ TTyRec (MkRVar ("r" ++ show i)) resType
        else return resType

