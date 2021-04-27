module TypeAutomata.FromAutomaton ( autToType ) where

import Syntax.CommonTerm
import Syntax.Types
import TypeAutomata.Definition
import Utils

import Control.Monad.State
import Control.Monad.Reader
import Data.Maybe (fromJust)

import Data.List (intersect, maximumBy)
import Data.Ord (comparing)
import Data.Graph.Inductive.PatriciaTree
import Data.Functor.Identity
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M

import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS (dfs)

-------------------------------------------------------------------------------------
-- Flow analysis
-------------------------------------------------------------------------------------

type FlowGraph = Gr () ()

-- | Generate a graph consisting only of the flow_edges of the type automaton.
genFlowGraph :: TypeAutCore a -> FlowGraph
genFlowGraph TypeAutCore{..} = mkGraph [(n,()) | n <- nodes ta_gr] [(i,j,()) | (i,j) <- ta_flowEdges]

flowComponent :: FlowGraph -> Node -> [Node]
flowComponent flgr i =
  let
    ns = neighbors flgr i
  in
    if null ns
      then [i]
      else ns ++ (foldr1 intersect) (map (neighbors flgr) ns)

freshTVar :: State Int TVar
freshTVar = do
  n <- get
  modify (+1)
  return (MkTVar ("t" ++ show n))

flowAnalysisState :: FlowGraph -> State Int (Map Node (Set TVar))
flowAnalysisState flgr =
    let
      nextNode = maximumBy (comparing (length . flowComponent flgr)) (nodes flgr)
      comp = flowComponent flgr nextNode
      newGr = delEdges [(x,y) | (x,y) <- edges flgr, x `elem` comp, y `elem` comp] flgr
    in
      if length comp < 2
        then return (M.fromList [(n,S.empty) | n <- nodes flgr])
        else do
          tv <- freshTVar
          rest <- flowAnalysisState newGr
          return $ foldr (.) id (map (M.adjust (S.insert tv)) comp) rest

getFlowAnalysisMap :: TypeAutCore EdgeLabelNormal -> Map Node (Set TVar)
getFlowAnalysisMap aut = fst $ runState (flowAnalysisState (genFlowGraph aut)) 0

initializeFromAutomaton :: TypeAutDet pol -> AutToTypeState
initializeFromAutomaton aut@TypeAut{..} =
  let
    flowAnalysis = getFlowAnalysisMap ta_core
  in
    AutToTypeState { tvMap = flowAnalysis
                   , graph = ta_gr ta_core
                   , cache = S.empty
                   , tvars = S.toList $ S.unions (M.elems flowAnalysis)
                   }

--------------------------------------------------------------------------
-- Type automata -> Types
--------------------------------------------------------------------------

data AutToTypeState = AutToTypeState { tvMap :: Map Node (Set TVar)
                                     , graph :: TypeGr
                                     , cache :: Set Node
                                     , tvars :: [TVar]
                                     }

type AutToTypeM a = Reader AutToTypeState a

autToType :: TypeAutDet pol -> TypeScheme pol
autToType aut@TypeAut{..} =
  let
    startState = initializeFromAutomaton aut
    monotype = runReader (nodeToType ta_pol (runIdentity ta_starts)) startState
  in
    TypeScheme (tvars startState) monotype

visitNode :: Node -> AutToTypeState -> AutToTypeState
visitNode i aut@AutToTypeState { graph, cache } =
  aut { graph = delEdges [(i,n) | n <- suc graph i, i `elem` dfs [n] graph] graph
      , cache = S.insert i cache }

checkCache :: Node -> AutToTypeM Bool
checkCache i = do
  cache <- asks cache
  return (i `S.member` cache)

nodeToTVars :: PolarityRep pol -> Node -> AutToTypeM [Typ pol]
nodeToTVars rep i = do
  tvMap <- asks tvMap
  return (TyVar rep <$> (S.toList $ fromJust $ M.lookup i tvMap))

nodeToOuts :: Node -> AutToTypeM [(EdgeLabelNormal, Node)]
nodeToOuts i = do
  gr <- asks graph
  let (_,_,_,outs) = context gr i
  return outs

-- | Compute the Nodes which have to be turned into the argument types for one constructor or destructor.
computeArgNodes :: [(EdgeLabelNormal, Node)] -- ^ All the outgoing edges of a node.
                -> DataCodata -- ^ Whether we want to construct a constructor or destructor
                -> XtorLabel -- ^ The Label of the constructor / destructor
                -> Twice [[Node]] -- ^ The nodes which contain the arguments of the constructor / destructor
computeArgNodes outs dc MkXtorLabel { labelName, labelPrdArity, labelCnsArity } =
  let
    prdFun n = [ node | ((EdgeSymbol dc' xt pc pos), node) <- outs, dc' == dc, xt == labelName, pc == Prd, pos == n]
    prdArgs = prdFun <$> [0..(labelPrdArity - 1)]
    cnsFun n = [ node | ((EdgeSymbol dc' xt pc pos), node) <- outs, dc' == dc, xt == labelName, pc == Cns, pos == n]
    cnsArgs = cnsFun <$> [0..(labelCnsArity - 1)]
  in
    Twice prdArgs cnsArgs

-- | Takes the output of computeArgNodes and turns the nodes into types.
argNodesToArgTypes :: Twice [[Node]] -> PolarityRep pol -> AutToTypeM (TypArgs pol)
argNodesToArgTypes (Twice prdNodes cnsNodes) rep = do
  prdTypes <- forM prdNodes $ \ns -> do
    typs <- forM ns $ \n -> do
      nodeToType rep n
    return $ case typs of [t] -> t; _ -> TySet rep typs
  cnsTypes <- forM cnsNodes $ \ns -> do
    typs <- forM ns $ \n -> do
      nodeToType (flipPolarityRep rep) n
    return $ case typs of [t] -> t; _ -> TySet (flipPolarityRep rep) typs
  return (MkTypArgs prdTypes cnsTypes)

nodeToType :: PolarityRep pol -> Node -> AutToTypeM (Typ pol)
nodeToType rep i = do
  -- First we check if i is in the cache.
  -- If i is in the cache, we return a recursive variable.
  inCache <- checkCache i
  case inCache of
    True -> return $ TyVar rep (MkTVar ("r" ++ show i))
    False -> nodeToTypeNoCache rep i

-- | Should only be called if node is not in cache.
nodeToTypeNoCache :: PolarityRep pol -> Node -> AutToTypeM (Typ pol)
nodeToTypeNoCache rep i = do
  outs <- nodeToOuts i
  gr <- asks graph
  let (Just (MkNodeLabel _ datSet codatSet tns)) = lab gr i
  let (maybeDat,maybeCodat) = (S.toList <$> datSet, S.toList <$> codatSet)
  resType <- local (visitNode i) $ do
    -- Creating type variables
    varL <- nodeToTVars rep i
    -- Creating data types
    datL <- case maybeDat of
      Nothing -> return []
      Just xtors -> do
        sig <- forM xtors $ \xt -> do
          let nodes = computeArgNodes outs Data xt
          argTypes <- argNodesToArgTypes nodes rep
          return (MkXtorSig (labelName xt) argTypes)
        return [TyData rep sig]
    -- Creating codata types
    codatL <- case maybeCodat of
      Nothing -> return []
      Just xtors -> do
        sig <- forM xtors $ \xt -> do
          let nodes = computeArgNodes outs Codata xt
          argTypes <- argNodesToArgTypes nodes (flipPolarityRep rep)
          return (MkXtorSig (labelName xt) argTypes)
        return [TyCodata rep sig]
    -- Creating Nominal types
    let nominals = TyNominal rep <$> (S.toList tns)
    let typs = varL ++ datL ++ codatL ++ nominals
    return $ case typs of [t] -> t; _ -> TySet rep typs

  -- If the graph is cyclic, make a recursive type
  if i `elem` dfs (suc gr i) gr
    then return $ TyRec rep (MkTVar ("r" ++ show i)) resType
    else return resType
