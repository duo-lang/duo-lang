module TypeAutomata.FromAutomaton ( autToType ) where

import Syntax.CommonTerm
import Syntax.Types
import Pretty.TypeAutomata ()
import TypeAutomata.Definition
import Utils

import Control.Monad.Except
import Control.Monad.State
    ( MonadState(get), runState, State, modify )
import Control.Monad.Reader

import Errors
import Data.Maybe (fromJust)
import Data.List (intersect, maximumBy)
import Data.Ord (comparing)
import Data.Graph.Inductive.PatriciaTree
import Data.Functor.Identity
import Data.Set (Set)
import Data.Set qualified as S
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T

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
  return (MkTVar ("t" <> T.pack (show n)))

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
initializeFromAutomaton TypeAut{..} =
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
type AutToTypeM a = (ReaderT AutToTypeState (Except Error)) a

runAutToTypeM :: AutToTypeM a -> AutToTypeState -> Either Error a
runAutToTypeM m state = runExcept (runReaderT m state)

autToType :: TypeAutDet pol -> Either Error (TypeScheme pol)
autToType aut@TypeAut{..} = do
  let startState = initializeFromAutomaton aut
  monotype <- runAutToTypeM (nodeToType ta_pol (runIdentity ta_starts)) startState
  return $ TypeScheme (tvars startState) monotype

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
                -> [(PrdCns,[Node])] -- ^ The nodes which contain the arguments of the constructor / destructor
computeArgNodes outs dc MkXtorLabel { labelName, labelArity } = args
  where
    argFun (n,pc) = (pc, [ node | ((EdgeSymbol dc' xt pc' pos), node) <- outs, dc' == dc, xt == labelName, pc == pc', pos == n])
    args = argFun <$> (enumerate labelArity)
    

-- | Takes the output of computeArgNodes and turns the nodes into types.
argNodesToArgTypes :: [(PrdCns,[Node])] -> PolarityRep pol -> AutToTypeM (LinearContext pol)
argNodesToArgTypes argNodes rep = do
  argTypes <- forM argNodes $ \ns -> do
    case ns of
      (Prd, ns) -> do
         typs <- forM ns (nodeToType rep)
         return $ case typs of [t] -> PrdType t; _ -> PrdType (TySet rep typs)
      (Cns, ns) -> do
         typs <- forM ns (nodeToType (flipPolarityRep rep))
         return $ case typs of [t] -> CnsType t; _ -> CnsType (TySet (flipPolarityRep rep) typs)
  return argTypes

nodeToType :: PolarityRep pol -> Node -> AutToTypeM (Typ pol)
nodeToType rep i = do
  -- First we check if i is in the cache.
  -- If i is in the cache, we return a recursive variable.
  inCache <- checkCache i
  case inCache of
    True -> return $ TyVar rep (MkTVar ("r" <> T.pack (show i)))
    False -> nodeToTypeNoCache rep i

-- | Should only be called if node is not in cache.
nodeToTypeNoCache :: PolarityRep pol -> Node -> AutToTypeM (Typ pol)
nodeToTypeNoCache rep i = do
  outs <- nodeToOuts i
  gr <- asks graph
  let (Just (MkNodeLabel _ datSet codatSet tns refDat refCodat)) = lab gr i
  let (maybeDat,maybeCodat) = (S.toList <$> datSet, S.toList <$> codatSet)
  let refDatTypes = M.toList refDat -- Unique data ref types
  let refCodatTypes = M.toList refCodat -- Unique codata ref types
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
        return [TyData rep Nothing sig]
    -- Creating codata types
    codatL <- case maybeCodat of
      Nothing -> return []
      Just xtors -> do
        sig <- forM xtors $ \xt -> do
          let nodes = computeArgNodes outs Codata xt
          argTypes <- argNodesToArgTypes nodes (flipPolarityRep rep)
          return (MkXtorSig (labelName xt) argTypes)
        return [TyCodata rep Nothing sig]
    -- Creating ref data types
    refDatL <- do
      forM refDatTypes $ \(tn,xtors) -> do
        sig <- forM (S.toList xtors) $ \xt -> do
          let nodes = computeArgNodes outs Data xt
          argTypes <- argNodesToArgTypes nodes rep
          return (MkXtorSig (labelName xt) argTypes)
        return $ TyData rep (Just tn) sig
    -- Creating ref codata types
    refCodatL <- do
      forM refCodatTypes $ \(tn,xtors) -> do
        sig <- forM (S.toList xtors) $ \xt -> do
          let nodes = computeArgNodes outs Codata xt
          argTypes <- argNodesToArgTypes nodes (flipPolarityRep rep)
          return (MkXtorSig (labelName xt) argTypes)
        return $ TyCodata rep (Just tn) sig
    -- Creating Nominal types
    let nominals = TyNominal rep <$> S.toList tns

    let typs = varL ++ datL ++ codatL ++ refDatL ++ refCodatL ++ nominals
    return $ case typs of [t] -> t; _ -> TySet rep typs

  -- If the graph is cyclic, make a recursive type
  if i `elem` dfs (suc gr i) gr
    then return $ TyRec rep (MkTVar ("r" <> T.pack (show i))) resType
    else return resType
