module TypeAutomata.FromAutomaton ( autToType ) where

import Syntax.Common
import Syntax.AST.Types
import Pretty.TypeAutomata ()
import TypeAutomata.Definition
import TypeAutomata.BicliqueDecomp
import Utils

import Control.Monad.Except
import Control.Monad.Reader

import Errors
import Data.Maybe (fromJust)
import Data.Functor.Identity
import Data.Set (Set)
import Data.Set qualified as S
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS (dfs)
import Data.Map

-- | Generate a graph consisting only of the flow_edges of the type automaton.
genFlowGraph :: TypeAutCore a -> FlowGraph
genFlowGraph TypeAutCore{..} = mkGraph [(n,()) | n <- nodes ta_gr] [(i,j,()) | (i,j) <- ta_flowEdges]

initializeFromAutomaton :: TypeAutDet pol -> AutToTypeState
initializeFromAutomaton TypeAut{..} =
  let
    flowAnalysis = computeFlowMap (genFlowGraph ta_core )
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
  return (TyVar rep Nothing <$> (S.toList $ fromJust $ M.lookup i tvMap))

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
    argFun (n,pc) = (pc, [ node | (EdgeSymbol dc' xt pc' pos, node) <- outs, dc' == dc, xt == labelName, pc == pc', pos == n])
    args = argFun <$> enumerate labelArity


-- | Takes the output of computeArgNodes and turns the nodes into types.
argNodesToArgTypes :: [(PrdCns,[Node])] -> PolarityRep pol -> AutToTypeM (LinearContext pol)
argNodesToArgTypes argNodes rep = do
  forM argNodes $ \ns -> do
    case ns of
      (Prd, ns) -> do
         typs <- forM ns (nodeToType rep)
         return $ case typs of [t] -> PrdCnsType PrdRep t; _ -> PrdCnsType PrdRep (TySet rep Nothing typs)
      (Cns, ns) -> do
         typs <- forM ns (nodeToType (flipPolarityRep rep))
         return $ case typs of [t] -> PrdCnsType CnsRep t; _ -> PrdCnsType CnsRep (TySet (flipPolarityRep rep) Nothing typs)

nodeToType :: PolarityRep pol -> Node -> AutToTypeM (Typ pol)
nodeToType rep i = do
  -- First we check if i is in the cache.
  -- If i is in the cache, we return a recursive variable.
  inCache <- checkCache i
  if inCache then
    return $ TyVar rep Nothing (MkTVar ("r" <> T.pack (show i)))
  else
    nodeToTypeNoCache rep i

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
    let adjEdges = lsuc gr i
    let typeArgsMap = fromList [((tn, i), t) | (t, TypeArgEdge tn _ i) <- adjEdges]
    let unsafeLookup = \k -> case Data.Map.lookup k typeArgsMap of
          Just x -> pure x
          Nothing -> throwOtherError ["Impossible: Cannot loose type arguments in automata"]
    nominals <- do
        forM (S.toList tns) $ \(tn, ncon, ncov) -> do
          conNodes <- sequence [ unsafeLookup (tn, i) | i <- [0 .. ncon-1] ]
          covNodes <- sequence [ unsafeLookup (tn, ncon + i) | i <- [0 .. ncov-1] ]
          conArgs <- sequence (nodeToType (flipPolarityRep rep) <$> conNodes)
          covArgs <- sequence (nodeToType rep <$> covNodes)
          pure $ TyNominal rep Nothing tn conArgs covArgs

    let typs = varL ++ datL ++ codatL ++ refDatL ++ refCodatL ++ nominals
    return $ case typs of [t] -> t; _ -> TySet rep Nothing typs

  -- If the graph is cyclic, make a recursive type
  if i `elem` dfs (suc gr i) gr
    then return $ TyRec rep (MkTVar ("r" <> T.pack (show i))) resType
    else return resType
