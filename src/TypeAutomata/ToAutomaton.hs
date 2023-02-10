module TypeAutomata.ToAutomaton ( typeToAut ) where


import Control.Monad.Except ( runExcept, Except )
import Control.Monad.Reader
    ( ReaderT(..), asks, MonadReader(..) )
import Control.Monad.State
    ( StateT(..), gets, modify )
import Data.Graph.Inductive.Graph (Node)
import Data.Graph.Inductive.Graph qualified as G
import Data.List.NonEmpty (NonEmpty)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set qualified as S
import Data.List.NonEmpty qualified as NE

import Errors ( Error, throwAutomatonError )
import Pretty.Types ()
import Pretty.Pretty (ppPrint)
import Syntax.TST.Types
import Syntax.RST.Types (PolarityRep(..), Polarity(..), polarityRepToPol)
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCnsRep(..), PrdCns(..))
import Syntax.CST.Names
import Syntax.CST.Kinds
import TypeAutomata.Definition
import Loc ( defaultLoc )
import Utils ( enumerate )
import Control.Monad

--------------------------------------------------------------------------
-- The TypeToAutomaton (TTA) Monad
--------------------------------------------------------------------------

-- | The lookup environment allows to map TVars to Nodes:
--
-- Recursive type variables have a polarity. They are therefore mapped to
-- either `(Just n, Nothing)` or `(Nothing, Just n)`
--
-- Skolem variables exist both positively and negatively. They are therefore
-- mapped to a pair `(n,m)`
data LookupEnv = LookupEnv { tSkolemVarEnv :: Map SkolemTVar (Node,Node) , tRecVarEnv :: Map RecTVar (Maybe Node, Maybe Node)}

type TTA a = StateT (TypeAutCore EdgeLabelEpsilon) (ReaderT LookupEnv (Except (NonEmpty Error))) a

runTypeAut :: TypeAutCore EdgeLabelEpsilon
           -- ^ The initial TypeAutomaton to start the computation.
           -> LookupEnv
           -- ^ The initial lookup environment.
           -> TTA a
           -- ^ The computation to run.
           -> Either (NonEmpty Error) (a, TypeAutCore EdgeLabelEpsilon)
runTypeAut graph lookupEnv f = runExcept (runReaderT (runStateT f graph) lookupEnv)


-- | Every type variable is mapped to a pair of nodes.
createNodes :: [KindedSkolem] -> [(SkolemTVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)]
createNodes tvars = createNode <$> createPairs tvars
  where
    createNode :: (KindedSkolem, Node, Node) -> (SkolemTVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)
    createNode ((tv, mk), posNode, negNode) = (tv, (posNode, emptyNodeLabel Pos (MkPknd mk)), (negNode, emptyNodeLabel Neg (MkPknd mk)), (negNode, posNode))

    createPairs :: [KindedSkolem] -> [(KindedSkolem, Node,Node)]
    createPairs tvs = (\i -> (tvs !! i, 2 * i, 2 * i + 1)) <$> [0..length tvs - 1]


initialize :: [KindedSkolem] -> (TypeAutCore EdgeLabelEpsilon, LookupEnv)
initialize tvars =
  let
    nodes = createNodes tvars
    initAut = TypeAutCore
              { ta_gr = G.mkGraph ([pos | (_,pos,_,_) <- nodes] ++ [neg | (_,_,neg,_) <- nodes]) []
              , ta_flowEdges = [ flowEdge | (_,_,_,flowEdge) <- nodes]
              }
    lookupEnv = LookupEnv { tSkolemVarEnv = M.fromList [(tv, (posNode,negNode)) | (tv,(posNode,_),(negNode,_),_) <- nodes]
                          , tRecVarEnv = M.empty
                          }
  in
    (initAut, lookupEnv)

-- | An alternative to `runTypeAut` where the initial state is constructed from a list of Tvars.
runTypeAutTvars :: [KindedSkolem]
                -> TTA a
                -> Either (NonEmpty Error) (a, TypeAutCore EdgeLabelEpsilon)
runTypeAutTvars tvars m = do
  let (aut, env) = initialize tvars
  runTypeAut aut env m

--------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------

modifyGraph :: (TypeGrEps -> TypeGrEps) -> TTA ()
modifyGraph f = modify go
  where
    go aut@TypeAutCore { ta_gr } = aut { ta_gr = f ta_gr }

insertNode :: Node -> NodeLabel -> TTA ()
insertNode node nodelabel = modifyGraph (G.insNode (node, nodelabel))

insertEdges :: [(Node,Node,EdgeLabelEpsilon)] -> TTA ()
insertEdges edges = modifyGraph (G.insEdges edges)

newNodeM :: TTA Node
newNodeM = do
  graph <- gets ta_gr
  pure $ (head . G.newNodes 1) graph

lookupTVar :: PolarityRep pol -> SkolemTVar -> TTA Node
lookupTVar PosRep tv = do
  tSkolemVarEnv <- asks tSkolemVarEnv
  case M.lookup tv tSkolemVarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The type variable:"
                                              , "    " <> unSkolemTVar tv
                                              , "is not available in the automaton."
                                              ]
    -- Skolem Variables cannot appear with only one polarity anymore
    --Just (Nothing,_) -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
    --                                                   , "The type variable:"
    --                                                   , "    " <> unSkolemTVar tv
    --                                                   , "exists only at negative polarity."
    --                                                   ]
    Just (pos,_) -> return pos
lookupTVar NegRep tv = do
  tSkolemVarEnv <- asks tSkolemVarEnv
  case M.lookup tv tSkolemVarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The type variable:"
                                              , "    " <> unSkolemTVar tv
                                              , "is not available in the automaton."
                                              ]
    -- Skolem Variables cannot appear with only one polarity anymore
    --Just (_,Nothing) -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
    --                                                   , "The type variable:"
    --                                                   , "    " <> unSkolemTVar tv
    --                                                   , "exists only at positive polarity."
    --                                                   ]
    Just (_,neg) -> return neg

lookupTRecVar :: PolarityRep pol -> RecTVar -> TTA Node
lookupTRecVar PosRep tv = do
  tRecVarEnv <- asks tRecVarEnv
  case M.lookup tv tRecVarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The Recursive Variable:"
                                              , "   " <> unRecTVar tv
                                              , "is not available in the automaton."
                                              ]
    Just (Nothing,_) -> throwAutomatonError defaultLoc ["Could not insert type into automaton."
                                                       , "The Recursive Variable:"
                                                       , "   " <> unRecTVar tv
                                                       , "exists only in negative polarity."
                                                       ]
    Just (Just pos,_) -> return pos
lookupTRecVar NegRep tv = do
  tRecVarEnv <- asks tRecVarEnv
  case M.lookup tv tRecVarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The Recursive Variable:"
                                              , "   " <> unRecTVar tv
                                              , "is not available in the automaton."
                                              ]
    Just (_,Nothing) -> throwAutomatonError defaultLoc ["Could not insert type into automaton."
                                                       , "The Recursive Variable:"
                                                       , "   " <> unRecTVar tv
                                                       , "exists only in positive polarity."
                                                       ]
    Just (_,Just neg) -> return neg



--------------------------------------------------------------------------
-- Inserting a type into an automaton
--------------------------------------------------------------------------

sigToLabel :: XtorSig pol -> XtorLabel
sigToLabel (MkXtorSig name ctxt) = MkXtorLabel name (linearContextToArity ctxt)

insertXtors :: CST.DataCodata -> PolarityRep pol1 -> Maybe (RnTypeName, Maybe RecTVar) -> PolyKind -> [XtorSig pol] -> TTA Node
insertXtors dc rep mtn pk xtors = do
  newNode <- newNodeM
  insertNode newNode (singleNodeLabelXtor (polarityRepToPol rep) dc mtn (S.fromList (sigToLabel <$> xtors)) pk)
  forM_ xtors $ \(MkXtorSig xt ctxt) -> do
    forM_ (enumerate ctxt) $ \(i, pcType) -> 
      case mtn of 
        Just (_, Just rv) -> do
          let extendEnv PosRep (LookupEnv tSkolemVars tRecVars) = LookupEnv tSkolemVars $ M.insert rv (Just newNode, Nothing) tRecVars
              extendEnv NegRep (LookupEnv tSkolemVars tRecVars) = LookupEnv tSkolemVars $ M.insert rv (Nothing, Just newNode) tRecVars
          n <- local (extendEnv rep) (insertPCType pcType) 
          insertEdges [(newNode, n, EdgeSymbol dc xt (case pcType of (PrdCnsType PrdRep _)-> Prd; (PrdCnsType CnsRep _) -> Cns) i)] 
        _ -> do
          node <- insertPCType pcType
          insertEdges [(newNode, node, EdgeSymbol dc xt (case pcType of (PrdCnsType PrdRep _)-> Prd; (PrdCnsType CnsRep _) -> Cns) i)] 
  return newNode

insertPCType :: PrdCnsType pol -> TTA Node
insertPCType (PrdCnsType _ ty) = insertType ty

insertVariantType :: VariantType pol -> TTA (Node, Variance)
insertVariantType (CovariantType ty) = do
  node <- insertType ty
  pure (node, Covariant)
insertVariantType (ContravariantType ty) = do
  node <- insertType ty
  pure (node, Contravariant)

insertType :: Typ pol -> TTA Node
insertType (TySkolemVar _ rep _ tv) = lookupTVar rep tv
insertType (TyUniVar loc _ _ tv) = throwAutomatonError loc  [ "Could not insert type into automaton."
                                                            , "The unification variable:"
                                                            , "    " <> unUniTVar tv
                                                            , "should not appear at this point in the program."
                                                            ]
insertType (TyRecVar _ rep _ tv) = lookupTRecVar rep tv
insertType (TyTop _ knd) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Neg knd)
  pure newNode
insertType (TyBot _ knd) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Pos knd)
  pure newNode
insertType (TyUnion _ knd ty1 ty2) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Pos knd)
  ty1' <- insertType ty1
  ty2' <- insertType ty2
  insertEdges [(newNode, ty1', EpsilonEdge ()), (newNode, ty2', EpsilonEdge ())]
  pure newNode
insertType (TyInter _ knd ty1 ty2) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Neg knd)
  ty1' <- insertType ty1
  ty2' <- insertType ty2
  insertEdges [(newNode, ty1', EpsilonEdge ()), (newNode, ty2', EpsilonEdge ())]
  pure newNode
insertType (TyRec _ rep rv ty) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel pol (getKind ty))
  let extendEnv PosRep (LookupEnv tSkolemVars tRecVars) = LookupEnv tSkolemVars $ M.insert rv (Just newNode, Nothing) tRecVars
      extendEnv NegRep (LookupEnv tSkolemVars tRecVars) = LookupEnv tSkolemVars $ M.insert rv (Nothing, Just newNode) tRecVars
  n <- local (extendEnv rep) (insertType ty)
  insertEdges [(newNode, n, EpsilonEdge ())]
  return newNode
insertType (TyData _  polrep eo xtors)   = insertXtors CST.Data   polrep Nothing (MkPolyKind [] eo) xtors
insertType (TyCodata _ polrep eo  xtors) = insertXtors CST.Codata polrep Nothing (MkPolyKind [] eo) xtors
insertType (TyDataRefined _ polrep pk mtn Nothing xtors)   = insertXtors CST.Data   polrep (Just (mtn,Nothing)) pk xtors
insertType (TyDataRefined _ polrep pk mtn (Just rv) xtors) = insertXtors CST.Data   polrep (Just (mtn,if rv `elem` recTVars xtors then Just rv else Nothing)) pk xtors
insertType (TyCodataRefined _ polrep pk mtn Nothing xtors)   = insertXtors CST.Codata polrep (Just (mtn,Nothing)) pk xtors
insertType (TyCodataRefined _ polrep pk mtn (Just rv) xtors) = insertXtors CST.Codata polrep (Just (mtn,if rv `elem` recTVars xtors then Just rv else Nothing)) pk xtors

insertType (TySyn _ _ _ ty) = insertType ty
insertType (TyApp _ _ (TyNominal _ rep polyknd tn) args) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (singleNodeLabelNominal pol (tn, NE.toList $ toVariance <$> args) polyknd)
  argNodes <- forM args insertVariantType
  insertEdges ((\(i, (n, variance)) -> (newNode, n, TypeArgEdge tn variance i)) <$> enumerate (NE.toList argNodes))
  return newNode
insertType (TyNominal _ rep polyknd tn) = do
  case kindArgs polyknd of 
    [] -> do
      let pol = polarityRepToPol rep 
      newNode <- newNodeM
      insertNode newNode (singleNodeLabelNominal pol (tn,[]) polyknd )
      return newNode
    _ -> throwAutomatonError defaultLoc ["Nominal type "<> ppPrint tn <> "was not fully applied"]
insertType (TyApp _ _ (TyRecVar _ rep pknd _) args) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel pol (MkPknd pknd))
  argNodes <- mapM insertVariantType args
  insertEdges ((\(_, (n, _)) -> (newNode, n, EpsilonEdge ())) <$> enumerate (NE.toList argNodes))
  return newNode
insertType (TyApp _ _ (TyDataRefined _ rep  pknd _ _ _) args) = do 
  let pol = polarityRepToPol rep 
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel pol (MkPknd pknd))
  argNodes <- mapM insertVariantType args
  insertEdges ((\(_, (n, _)) -> (newNode, n, EpsilonEdge ())) <$> enumerate (NE.toList argNodes))
  return newNode
insertType (TyApp _ _ (TyCodataRefined _ rep  pknd _ _ _) args) = do 
  let pol = polarityRepToPol rep 
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel pol (MkPknd pknd))
  argNodes <- mapM insertVariantType args
  insertEdges ((\(_, (n, _)) -> (newNode, n, EpsilonEdge ())) <$> enumerate (NE.toList argNodes))
  return newNode

insertType TyApp{} = throwAutomatonError defaultLoc ["Types can only be applied to nominal types"]
insertType (TyI64 _ rep) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol I64)
  return newNode
insertType (TyF64 _ rep) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol F64)
  return newNode
insertType (TyChar _ rep) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol PChar)
  return newNode
insertType (TyString _ rep) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol PString)
  return newNode
insertType (TyFlipPol _ _) =
  throwAutomatonError defaultLoc ["Tried to insert TyFlipPol into type automaton"]

--------------------------------------------------------------------------
--
--------------------------------------------------------------------------


-- turns a type into a type automaton with prescribed start polarity.
typeToAut :: TypeScheme pol -> Either (NonEmpty Error) (TypeAutEps pol)
typeToAut TypeScheme { ts_vars, ts_monotype } = do
  (start, aut) <- runTypeAutTvars ts_vars (insertType ts_monotype)
  return TypeAut { ta_pol = getPolarity ts_monotype
                 , ta_starts = [start]
                 , ta_core = aut
                 }
