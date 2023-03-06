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
import Pretty.Pretty
import Syntax.TST.Types
import Syntax.RST.Types (PolarityRep(..), Polarity(..), polarityRepToPol, getTypeNames)
import Translate.EmbedTST
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
data LookupEnv = LookupEnv { tSkolemVarEnv :: Map SkolemTVar (Node,Node) , tRecVarEnv :: Map RecTVar (Maybe Node, Maybe Node), tyArgEnv :: Map RnTypeName [(Node,Variance)] }

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
                          , tyArgEnv = M.empty
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
    go aut = aut { ta_gr = f aut.ta_gr }

insertNode :: Node -> NodeLabel -> TTA ()
insertNode node nodelabel = modifyGraph (G.insNode (node, nodelabel))

insertEdges :: [(Node,Node,EdgeLabelEpsilon)] -> TTA ()
insertEdges edges = modifyGraph (G.insEdges edges)

newNodeM :: TTA Node
newNodeM = do
  graph <- gets (\x -> x.ta_gr)
  pure $ (head . G.newNodes 1) graph

lookupTVar :: PolarityRep pol -> SkolemTVar -> TTA Node
lookupTVar PosRep tv = do
  tSkolemVarEnv <- asks (\x -> x.tSkolemVarEnv)
  case M.lookup tv tSkolemVarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The type variable:"
                                              , "    " <> tv.unSkolemTVar
                                              , "is not available in the automaton."
                                              ]
    Just (pos,_) -> return pos
lookupTVar NegRep tv = do
  tSkolemVarEnv <- asks (\x -> x.tSkolemVarEnv)
  case M.lookup tv tSkolemVarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The type variable:"
                                              , "    " <> tv.unSkolemTVar
                                              , "is not available in the automaton."
                                              ]
    Just (_,neg) -> return neg

lookupTRecVar :: PolarityRep pol -> RecTVar -> TTA Node
lookupTRecVar PosRep tv = do
  tRecVarEnv <- asks (\x -> x.tRecVarEnv)
  case M.lookup tv tRecVarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The Recursive Variable:"
                                              , "   " <> tv.unRecTVar
                                              , "is not available in the automaton."
                                              ]
    Just (Nothing,_) -> throwAutomatonError defaultLoc ["Could not insert type into automaton."
                                                       , "The Recursive Variable:"
                                                       , "   " <> tv.unRecTVar
                                                       , "exists only in negative polarity."
                                                       ]
    Just (Just pos,_) -> return pos
lookupTRecVar NegRep tv = do
  tRecVarEnv <- asks (\x -> x.tRecVarEnv)
  case M.lookup tv tRecVarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The Recursive Variable:"
                                              , "   " <> tv.unRecTVar
                                              , "is not available in the automaton."
                                              ]
    Just (_,Nothing) -> throwAutomatonError defaultLoc ["Could not insert type into automaton."
                                                       , "The Recursive Variable:"
                                                       , "   " <> tv.unRecTVar
                                                       , "exists only in positive polarity."
                                                       ]
    Just (_,Just neg) -> return neg



--------------------------------------------------------------------------
-- Inserting a type into an automaton
--------------------------------------------------------------------------

sigToLabel :: XtorSig pol -> XtorLabel
sigToLabel (MkXtorSig name ctxt) = MkXtorLabel name (linearContextToArity ctxt)

insertXtors :: CST.DataCodata -> Polarity -> Maybe RnTypeName -> PolyKind -> [XtorSig pol] -> TTA Node
-- XData
insertXtors dc pol Nothing pk xtors = do 
  newNode <- newNodeM 
  let xtorLabel = singleNodeLabelXtor pol dc Nothing (S.fromList (sigToLabel <$> xtors)) pk
  insertNode newNode xtorLabel 
  forM_ xtors $ \(MkXtorSig xt ctxt) -> mapM_ (\x -> insertCtxt xt x newNode) (enumerate ctxt)
  return newNode
  where 
    insertCtxt :: XtorName -> (Int, PrdCnsType pol) -> Node -> TTA () 
    insertCtxt nm (i,pcType) newNode = do 
      n <- insertPCType pcType
      insertEdges [(newNode, n, EdgeSymbol dc nm (case pcType of (PrdCnsType PrdRep _) -> Prd; (PrdCnsType CnsRep _) -> Cns) i)]

-- XDataRefined with MonoKind
insertXtors dc pol (Just tyn) pk@(MkPolyKind [] _) xtors = do 
  newNode <- newNodeM
  let xtorLabel = singleNodeLabelXtor pol dc (Just (tyn,[])) (S.fromList (sigToLabel <$> xtors)) pk
  insertNode newNode xtorLabel 
  forM_ xtors $ \(MkXtorSig xt ctxt) -> mapM_ (\x -> insertCtxt xt x newNode) (enumerate ctxt)
  return newNode
  where 
    insertCtxt :: XtorName -> (Int, PrdCnsType pol) -> Node -> TTA () 
    insertCtxt nm (i,pcType) newNode = do 
      n <- insertPCType pcType
      insertEdges [(newNode, n, EdgeSymbol dc nm (case pcType of (PrdCnsType PrdRep _) -> Prd; (PrdCnsType CnsRep _) -> Cns) i)]

-- XDataRefined with PolyKind
insertXtors dc pol (Just tyn) pk xtors = do
  varsMap <- asks (\x -> x.tyArgEnv)
  vars <- case M.lookup tyn varsMap of Nothing -> throwAutomatonError defaultLoc ["type " <> ppPrint tyn <> " was not fully applied"]; Just vars -> return vars
  newNode <- newNodeM
  let xtorLabel = singleNodeLabelXtor pol dc (Just (tyn, snd <$> vars)) (S.fromList (sigToLabel <$> xtors)) pk
  insertNode newNode xtorLabel 
  insertEdges ((\(i,(n,variance)) -> (newNode, n, TypeArgEdge tyn variance i)) <$> enumerate vars)
  forM_ xtors $ \(MkXtorSig xt ctxt) -> mapM_ (\x -> insertCtxt xt x newNode) (enumerate ctxt)
  return newNode
  where 
    insertCtxt :: XtorName -> (Int, PrdCnsType pol) -> Node -> TTA () 
    insertCtxt nm (i,pcType) newNode = do 
      n <- insertPCType pcType
      insertEdges [(newNode, n, EdgeSymbol dc nm (case pcType of (PrdCnsType PrdRep _) -> Prd; (PrdCnsType CnsRep _) -> Cns) i)]

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
                                                            , "    " <> tv.unUniTVar
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
  let extendEnv PosRep (LookupEnv tSkolemVars tRecVars tArgs) = LookupEnv tSkolemVars (M.insert rv (Just newNode, Nothing) tRecVars) tArgs
      extendEnv NegRep (LookupEnv tSkolemVars tRecVars tArgs) = LookupEnv tSkolemVars (M.insert rv (Nothing, Just newNode) tRecVars) tArgs
  n <- local (extendEnv rep) (insertType ty)
  insertEdges [(newNode, n, EpsilonEdge ())]
  return newNode
insertType (TyData _  polrep eo xtors)   = insertXtors CST.Data   (polarityRepToPol polrep) Nothing (MkPolyKind [] eo) xtors
insertType (TyCodata _ polrep eo  xtors) = insertXtors CST.Codata (polarityRepToPol polrep) Nothing (MkPolyKind [] eo) xtors
insertType (TyDataRefined _ polrep pk mtn xtors)   = insertXtors CST.Data   (polarityRepToPol polrep) (Just mtn) pk xtors
insertType (TyCodataRefined _ polrep pk mtn xtors) = insertXtors CST.Codata (polarityRepToPol polrep) (Just mtn) pk xtors
insertType (TySyn _ _ _ ty) = insertType ty

insertType (TyApp _ _ ty args) = do 
  argNodes <- mapM insertVariantType args
  let tyns = getTypeNames (embedTST ty)
  case tyns of 
    [] -> insertType ty
    _ -> do
      tArgsMap <- asks (\x -> x.tyArgEnv)
      let newTyArgs = foldr (\tyn argsMap -> M.insert tyn (NE.toList argNodes) argsMap) tArgsMap tyns
      let extendEnv (LookupEnv tSkolemVars tRecVars _) = LookupEnv tSkolemVars tRecVars newTyArgs
      local extendEnv (insertType ty)

insertType (TyNominal _ rep pknd@(MkPolyKind [] _) tn) = do 
  let pol = polarityRepToPol rep 
  newNode <- newNodeM
  insertNode newNode (singleNodeLabelNominal pol (tn, []) pknd)
  return newNode 

insertType (TyNominal _ rep polyknd tn) = do
  let pol = polarityRepToPol rep 
  newNode <- newNodeM
  varsMap <- asks (\x -> x.tyArgEnv) 
  vars <- case M.lookup tn varsMap of Nothing -> throwAutomatonError defaultLoc ["Nominal Type " <> ppPrint tn <> " was not fully applied"]; Just vars -> return vars
  insertNode newNode (singleNodeLabelNominal pol (tn,map snd vars) polyknd )
  insertEdges ((\(i,(n,variance)) -> (newNode, n, TypeArgEdge tn variance i)) <$> enumerate vars)
  return newNode

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
typeToAut ts = do
  (start, aut) <- runTypeAutTvars ts.ts_vars (insertType ts.ts_monotype)
  return TypeAut { ta_pol = getPolarity ts.ts_monotype
                 , ta_starts = [start]
                 , ta_core = aut
                 }
