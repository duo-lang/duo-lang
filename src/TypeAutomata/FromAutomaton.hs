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
  return (TyTVar () Normal <$> (S.toList $ fromJust $ M.lookup i tvMap))

nodeToOuts :: Node -> AutToTypeM [(EdgeLabel, Node)]
nodeToOuts i = do
  gr <- asks graph
  let (_,_,_,outs) = context gr i
  return outs

-- | Compute the Nodes which have to be turned into the argument types for one constructor or destructor.
computeArgNodes :: [(EdgeLabel, Node)] -- ^ All the outgoing edges of a node.
                -> DataCodata -- ^ Whether we want to construct a constructor or destructor
                -> XtorName -- ^ The name of the constructor / destructor
                -> Twice [[Node]] -- ^ The nodes which contain the arguments of the constructor / destructor
computeArgNodes outs dc xt =
  let
    -- Filter out all Edges which don't interest us.
    filtereds pc = [ (el, n) | (el@(EdgeSymbol dc' xt' pc' _), n) <- outs, dc == dc', xt == xt', pc == pc' ]
    -- Sort the Edges by their position in the Arglist.
    sortFun (EdgeSymbol _ _ _ j1,_) (EdgeSymbol _ _ _ j2,_) = j1 `compare` j2
    sorteds pc = sortBy sortFun (filtereds pc)
    -- Group the nodes by their position.
    groupFun (EdgeSymbol _ _ _ j1,_) (EdgeSymbol _ _ _ j2,_) = j1 == j2
    groupeds pc = groupBy groupFun (sorteds pc)
    groupeds' pc = (fmap . fmap) snd $ groupeds pc
  in
    Twice (groupeds' Prd) (groupeds' Cns)

-- | Takes the output of computeArgNodes and turns the nodes into types.
argNodesToArgTypes :: Twice [[Node]] -> DataCodata -> PrdCns -> AutToTypeM (Twice [TargetType])
argNodesToArgTypes (Twice prdNodes cnsNodes) dc pol = do
  prdTypes <- forM prdNodes $ \ns -> do
    typs <- forM ns $ \n -> do
      nodeToType n
    return $ unionOrInter (applyVariance dc Prd pol) typs
  cnsTypes <- forM cnsNodes $ \ns -> do
    typs <- forM ns $ \n -> do
      nodeToType n
    return $ unionOrInter (applyVariance dc Cns pol) typs
  return (Twice prdTypes cnsTypes)

nodeToType :: Node -> AutToTypeM TargetType
nodeToType i = do
  -- First we check if i is in the cache.
  -- If i is in the cache, we return a recursive variable.
  inCache <- checkCache i
  case inCache of
    True -> return $ TyTVar () Recursive (MkTVar ("r" ++ show i))
    False -> do
      outs <- nodeToOuts i
      gr <- asks graph
      let (_,_,(pol,HeadCons datSet codatSet tns),_) = context gr i
      let (maybeDat,maybeCodat) = (S.toList <$> datSet, S.toList <$> codatSet)
      resType <- local (visitNode i) $ do
        -- Creating type variables
        varL <- nodeToTVars i
        -- Creating data types
        datL <- case maybeDat of
          Nothing -> return []
          Just xtors -> do
            sig <- forM xtors $ \xt -> do
              let nodes = computeArgNodes outs Data xt
              argTypes <- argNodesToArgTypes nodes Data pol
              return (MkXtorSig xt argTypes)
            return [TySimple Data sig]
        -- Creating codata types
        codatL <- case maybeCodat of
          Nothing -> return []
          Just xtors -> do
            sig <- forM xtors $ \xt -> do
              let nodes = computeArgNodes outs Codata xt
              argTypes <- argNodesToArgTypes nodes Codata pol
              return (MkXtorSig xt argTypes)
            return [TySimple Codata sig]
        -- Creating Nominal types
        let nominals = TyNominal <$> (S.toList tns)
        return $ unionOrInter pol (varL ++ datL ++ codatL ++ nominals)

      -- If the graph is cyclic, make a recursive type
      if i `elem` dfs (suc gr i) gr
        then return $ TyRec () (MkTVar ("r" ++ show i)) resType
        else return resType

