{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use tuple-section" #-}

module TypeAutomata.FromAutomaton ( autToType ) where

import Syntax.TST.Types
import Syntax.RST.Types (PolarityRep(..), flipPolarityRep)
import Syntax.RST.Names
import Syntax.RST.Kinds
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..), PolyKind(..), Variance(..))
import Syntax.CST.Names
import Pretty.TypeAutomata ()
import TypeAutomata.Definition
import TypeAutomata.BicliqueDecomp
import Utils ( enumerate )
import Loc ( defaultLoc )

import Control.Monad.Except
import Control.Monad.Reader

import Errors
import Data.Maybe (fromJust)
import Data.Functor.Identity
import Data.Set (Set)
import Data.Set qualified as S
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS (dfs)
import Data.List.NonEmpty (NonEmpty((:|)))


-- | Generate a graph consisting only of the flow_edges of the type automaton.
genFlowGraph :: TypeAutCore -> FlowGraph
genFlowGraph aut = mkGraph [(n,()) | n <- nodes aut.ta_gr] [(i,j,()) | (i,j) <- aut.ta_flowEdges]

initializeFromAutomaton :: TypeAutDet pol -> AutToTypeState
initializeFromAutomaton aut =
  let
    flowAnalysis = computeFlowMap (genFlowGraph aut.ta_core )

    gr = aut.ta_core.ta_gr
    getTVars :: (Node,Set SkolemTVar) -> [KindedSkolem]
    getTVars (nd,skolems) = do
      let skList = S.toList skolems
      let nl = lab gr nd
      let mk = case nl of Nothing -> error "Can't find Node Label (should never happen)"; Just nl -> getKindNL nl
      map (\x -> (x,mk)) skList
  in
    AutToTypeState { tvMap = flowAnalysis
                   , graph = gr
                   , cache = S.empty
                   , tvars = concatMap getTVars (M.toList flowAnalysis)
                   --S.toList $ S.unions (M.elems flowAnalysis)
                   }

--------------------------------------------------------------------------
-- Type automata -> Types
--------------------------------------------------------------------------

data AutToTypeState = AutToTypeState { tvMap :: Map Node (Set SkolemTVar)
                                     , graph :: TypeGr
                                     , cache :: Set Node
                                     , tvars :: [KindedSkolem]
                                     }
type AutToTypeM a = (ReaderT AutToTypeState (Except (NonEmpty Error))) a

runAutToTypeM :: AutToTypeM a -> AutToTypeState -> Either (NonEmpty Error) a
runAutToTypeM m state = runExcept (runReaderT m state)


autToType :: TypeAutDet pol -> Either (NonEmpty Error) (TypeScheme pol)
autToType aut = do
  let startState = initializeFromAutomaton aut
  monotype <- runAutToTypeM (nodeToType aut.ta_pol (runIdentity aut.ta_starts) Nothing) startState
  pure TypeScheme { ts_loc = defaultLoc
                  -- TODO Replace CBV with actual kinds
                  , ts_vars = startState.tvars
                  , ts_monotype = monotype
                  }

visitNode :: Node -> AutToTypeState -> AutToTypeState
visitNode i aut =
  aut { graph = delEdges [(i,n) | n <- suc aut.graph i, i `elem` dfs [n] aut.graph] aut.graph
      , cache = S.insert i aut.cache }

checkCache :: Node -> AutToTypeM Bool
checkCache i = do
  cache <- asks (\x -> x.cache)
  return (i `S.member` cache)

getNodeKindPk :: Node -> AutToTypeM PolyKind
getNodeKindPk i = do 
  gr <- asks (\x -> x.graph)
  case lab gr i of 
    Nothing -> throwAutomatonError  defaultLoc [T.pack ("Could not find Nodelabel of Node" <> show i)]
    Just (MkNodeLabel _ _ _ _ _ _ _ pk) -> return pk
    _ -> throwAutomatonError defaultLoc ["Recursive Variables can only have kind CBV or CBN"]

getNodeKind :: Node -> AutToTypeM AnyKind
getNodeKind i = do 
  gr <- asks (\x -> x.graph)
  case lab gr i of 
    Nothing -> throwAutomatonError  defaultLoc [T.pack ("Could not find Nodelabel of Node" <> show i)]
    Just (MkNodeLabel _ _ _ _ _ _ _ pk) -> return (MkPknd pk)
    Just MkPrimitiveNodeLabel{ pl_prim = pty } -> pure $ primitiveToAnyKind pty



nodeToTVars :: PolarityRep pol -> Node -> AutToTypeM [Typ pol]
nodeToTVars rep i = do
  tvMap <- asks (\x -> x.tvMap)
  knd <- getNodeKindPk i
  return (TySkolemVar defaultLoc rep (MkPknd knd) <$> S.toList (fromJust $ M.lookup i tvMap))

nodeToOuts :: Node -> AutToTypeM [(EdgeLabel, Node)]
nodeToOuts i = do
  gr <- asks (\x -> x.graph)
  let (_,_,_,outs) = context gr i
  return outs

-- | Compute the Nodes which have to be turned into the argument types for one constructor or destructor.
computeArgNodes :: [(EdgeLabel, Node)] -- ^ All the outgoing edges of a node.
                -> CST.DataCodata -- ^ Whether we want to construct a constructor or destructor
                -> XtorLabel -- ^ The Label of the constructor / destructor
                -> [(PrdCns,[Node])] -- ^ The nodes which contain the arguments of the constructor / destructor
computeArgNodes outs dc lbl = args
  where
    argFun (n,pc) = (pc, [ node | (EdgeSymbol dc' xt pc' pos, node) <- outs, dc' == dc, xt == lbl.labelName, pc == pc', pos == n])
    args = argFun <$> enumerate lbl.labelArity

-- | Takes the output of computeArgNodes and turns the nodes into types.
argNodesToArgTypes :: [(PrdCns,[Node])] -> PolarityRep pol -> PolarityRep pol1 -> Maybe (RnTypeName, NonEmpty (VariantType pol1)) -> AutToTypeM (LinearContext pol)
argNodesToArgTypes argNodes rep rep1 margs = do
  forM argNodes $ \ns -> do
    case ns of
      (Prd, ns) -> do
         let margs' = case (rep,rep1) of (PosRep,PosRep) -> margs; (NegRep,NegRep) -> margs; _ -> Nothing
         typs <- forM ns (\x -> nodeToType rep x margs')
         knds <- mapM getNodeKind ns
         knd <- checkTypKinds knds
         pure $ PrdCnsType PrdRep $ case rep of
                                       PosRep -> mkUnion defaultLoc knd typs
                                       NegRep -> mkInter defaultLoc knd typs
      (Cns, ns) -> do
         let margs' = case (rep,rep1) of (PosRep,NegRep) -> margs; (NegRep, PosRep) -> margs; _ -> Nothing
         typs <- forM ns (\x -> nodeToType (flipPolarityRep rep) x margs')
         knds <- mapM getNodeKind ns
         knd <- checkTypKinds knds
         pure $ PrdCnsType CnsRep $ case rep of
                                       PosRep -> mkInter defaultLoc knd typs
                                       NegRep -> mkUnion defaultLoc knd typs

checkTypKinds :: [AnyKind] -> AutToTypeM AnyKind
checkTypKinds [] = throwAutomatonError  defaultLoc [T.pack "Can't get Kind of empty list of types"]
checkTypKinds (fst:rst) = if all (fst ==) rst then return fst else throwAutomatonError defaultLoc [T.pack "Kinds of intersection types don't match"]

nodeToType :: PolarityRep pol -> Node -> Maybe (RnTypeName, NonEmpty (VariantType pol)) -> AutToTypeM (Typ pol)
nodeToType rep i margs = do
  -- First we check if i is in the cache.
  -- If i is in the cache, we return a recursive variable.
  inCache <- checkCache i
  if inCache
    then do 
      knd <- getNodeKindPk i
      let rvTy =  TyRecVar defaultLoc rep knd (MkRecTVar ("r" <> T.pack (show i)))
      case margs of 
        Nothing -> pure rvTy 
        Just (tyn, args) -> pure $ TyApp defaultLoc rep knd.returnKind rvTy tyn args
    else nodeToTypeNoCache rep i

-- | Should only be called if node is not in cache.
nodeToTypeNoCache :: PolarityRep pol -> Node -> AutToTypeM (Typ pol)
nodeToTypeNoCache rep i  = do
  gr <- asks (\x -> x.graph)
  case fromJust (lab gr i) of
    MkPrimitiveNodeLabel _ tp -> do
      let toPrimType :: PolarityRep pol -> PrimitiveType -> Typ pol
          toPrimType rep I64 = TyI64 defaultLoc rep
          toPrimType rep F64 = TyF64 defaultLoc rep
          toPrimType rep PChar = TyChar defaultLoc rep
          toPrimType rep PString = TyString defaultLoc rep
      pure (toPrimType rep tp)
    MkNodeLabel _ _ _ _ _ _ _ (KindVar _) -> throwAutomatonError defaultLoc ["Kind Variable should not appear in the program at this point"]
    MkNodeLabel _ datSet codatSet tns refDat refCodat skolems pk@(MkPolyKind _ _) -> do
      outs <- nodeToOuts i
      let (maybeDat,maybeCodat) = (S.toList <$> datSet, S.toList <$> codatSet)
      let refDatTypes = M.toList refDat -- Unique data ref types
      let refCodatTypes = M.toList refCodat -- Unique codata ref types
      let adjEdges = lsuc gr i
      let typeArgsMap :: Map (RnTypeName, Int) (Node, Variance) = M.fromList [((tn, i), (node,var)) | (node, TypeArgEdge tn var i) <- adjEdges]
      let unsafeLookup :: (RnTypeName, Int) -> AutToTypeM (Node,Variance) = \k -> case M.lookup k typeArgsMap of Just x -> pure x; Nothing -> throwOtherError defaultLoc ["Impossible: Cannot loose type arguments in automata"]
      resType <- local (visitNode i) $ do
        -- Creating type variables
        varL <- nodeToTVars rep i
        -- Creating data types
        datL <- case maybeDat of
          Nothing -> return []
          Just xtors -> do
            sig <- forM xtors $ \xt -> do
              let nodes = computeArgNodes outs CST.Data xt
              argTypes <- argNodesToArgTypes nodes rep rep Nothing
              return (MkXtorSig xt.labelName argTypes)
            return [TyData defaultLoc rep pk.returnKind sig]
        -- Creating codata types
        codatL <- case maybeCodat of
          Nothing -> return []
          Just xtors -> do
            sig <- forM xtors $ \xt -> do
              let nodes = computeArgNodes outs CST.Codata xt
              argTypes <- argNodesToArgTypes nodes (flipPolarityRep rep) rep Nothing
              return (MkXtorSig xt.labelName argTypes)
            return [TyCodata defaultLoc rep pk.returnKind sig]
        -- Creating ref data types
        refDatL <- do
          forM refDatTypes $ \(tn,(xtors,vars)) -> do
            argNodes <- sequence [ unsafeLookup (tn, i) | i <- [0..(length vars - 1)]]
            let f (node, Covariant) = CovariantType <$> nodeToType rep node Nothing
                f (node, Contravariant) = ContravariantType <$> nodeToType (flipPolarityRep rep) node Nothing
            args <- mapM f argNodes 
            sig <- forM (S.toList xtors) $ \xt -> do
              let nodes = computeArgNodes outs CST.Data xt
              let margs = case args of 
                            [] -> Nothing
                            (args1:argsRst) -> Just (tn, args1:|argsRst)
              argTypes <- argNodesToArgTypes nodes rep rep margs
              return (MkXtorSig xt.labelName argTypes)
            case args of 
              [] -> return $ TyDataRefined defaultLoc rep pk (snd <$> vars) tn sig'
              (arg1:argRst) -> return $ TyApp defaultLoc rep pk.returnKind (TyDataRefined defaultLoc rep pk (snd <$> vars) tn sig') tn (arg1:|argRst)
        -- Creating ref codata types
        refCodatL <- do
          forM refCodatTypes $ \(tn,(xtors,vars)) -> do
            argNodes <- sequence [ unsafeLookup (tn, i) | i <- [0..(length vars - 1)]]
            let f (node, Covariant) = CovariantType <$> nodeToType rep node Nothing 
                f (node, Contravariant) = ContravariantType <$> nodeToType (flipPolarityRep rep) node Nothing
            args <- mapM f argNodes 
            sig <- forM (S.toList xtors) $ \xt -> do
              let nodes = computeArgNodes outs CST.Codata xt
              let margs = case args of
                            [] -> Nothing
                            (args1:argsRst) -> Just (tn, args1:|argsRst)
              argTypes <- argNodesToArgTypes nodes (flipPolarityRep rep) rep margs
              return (MkXtorSig xt.labelName argTypes)
            case args of
              [] -> return $ TyCodataRefined defaultLoc rep pk (snd <$> vars) tn sig'
              (arg1:argRst) -> return $ TyApp defaultLoc rep pk.returnKind (TyCodataRefined defaultLoc rep pk (snd <$> vars) tn sig') tn (arg1:|argRst)
        -- Creating Nominal types
        nominals <- do
            forM (S.toList tns) $ \(tn, variances) -> do
              argNodes <- sequence [ unsafeLookup (tn, i) | i <- [0..(length variances - 1)]]
              let f (node, Covariant) = CovariantType <$> nodeToType rep node Nothing
                  f (node, Contravariant) = ContravariantType <$> nodeToType (flipPolarityRep rep) node Nothing
              args <- mapM f argNodes 
              case args of 
                [] -> pure $ TyNominal defaultLoc rep pk tn
                (fst:rst) -> pure $ TyApp defaultLoc rep pk.returnKind (TyNominal defaultLoc rep pk tn) tn (fst:|rst)

        let typs = varL ++ datL ++ codatL ++ refDatL ++ refCodatL ++ nominals -- ++ prims
        return $ case rep of
          PosRep -> mkUnion defaultLoc (MkPknd pk) typs
          NegRep -> mkInter defaultLoc (MkPknd pk) typs

      -- If the graph is cyclic, make a recursive type
      if i `elem` dfs (suc gr i) gr
        then return $ TyRec defaultLoc rep (MkRecTVar ("r" <> T.pack (show i))) resType
        else return resType
