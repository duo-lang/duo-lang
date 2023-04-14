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
import Syntax.RST.Types (PolarityRep(..), Polarity(..), polarityRepToPol)
import Syntax.RST.Names
import Syntax.RST.Kinds
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCnsRep(..), PrdCns(..))
import Syntax.CST.Names
import Syntax.CST.Kinds
import TypeAutomata.Definition
import Loc ( defaultLoc )
import Utils ( enumerate )

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
data LookupEnv = LookupEnv { tSkolemVarEnv :: Map SkolemTVar (Node,Node) , tRecVarEnv :: Map RecTVar (Maybe Node, Maybe Node) }

type TTA a = StateT TypeAutCore (ReaderT LookupEnv (Except (NonEmpty Error))) a

runTypeAut :: TypeAutCore
           -- ^ The initial TypeAutomaton to start the computation.
           -> LookupEnv
           -- ^ The initial lookup environment.
           -> TTA a
           -- ^ The computation to run.
           -> Either (NonEmpty Error) (a, TypeAutCore)
runTypeAut graph lookupEnv f = runExcept (runReaderT (runStateT f graph) lookupEnv)


-- | Every type variable is mapped to a pair of nodes.
createNodes :: [KindedSkolem] -> [(SkolemTVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)]
createNodes tvars = createNode <$> createPairs tvars
  where
    createNode :: (KindedSkolem, Node, Node) -> (SkolemTVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)
    createNode ((tv, mk), posNode, negNode) = (tv, (posNode, emptyNodeLabel Pos (MkPknd mk)), (negNode, emptyNodeLabel Neg (MkPknd mk)), (negNode, posNode))

    createPairs :: [KindedSkolem] -> [(KindedSkolem, Node,Node)]
    createPairs tvs = (\i -> (tvs !! i, 2 * i, 2 * i + 1)) <$> [0..length tvs - 1]


initialize :: [KindedSkolem] -> (TypeAutCore, LookupEnv)
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
                -> Either (NonEmpty Error) (a, TypeAutCore)
runTypeAutTvars tvars m = do
  let (aut, env) = initialize tvars
  runTypeAut aut env m

--------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------

modifyGraph :: (TypeGr -> TypeGr) -> TTA ()
modifyGraph f = modify go
  where
    go aut = aut { ta_gr = f aut.ta_gr }

insertNode :: Node -> NodeLabel -> TTA ()
insertNode node nodelabel = modifyGraph (G.insNode (node, nodelabel))

insertEdges :: [(Node,Node,EdgeLabel)] -> TTA ()
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

insertXtors :: CST.DataCodata -> Polarity -> Maybe (RnTypeName,[SkolemTVar]) -> PolyKind -> [XtorSig pol] -> TTA Node
insertXtors _ _ _ (KindVar _) _ = throwAutomatonError defaultLoc ["Kind variable can't appear at this point in the program"]
-- XData
insertXtors dc pol Nothing pk xtors = do 
  newNode <- newNodeM 
  let xtorLabel = singleNodeLabelXtor pol dc Nothing (S.fromList (sigToLabel <$> xtors)) pk
  insertNode newNode xtorLabel 
  mapM_ (\(MkXtorSig xt ctxt) -> mapM_ (insertCtxt newNode xt) (enumerate ctxt)) xtors
  return newNode
  where 
    insertCtxt :: Node -> XtorName -> (Int, PrdCnsType pol) -> TTA ()
    insertCtxt newNode nm (i,pcType) = do 
      ns <- insertPCType pcType
      insertEdges [(newNode, n, EdgeSymbol dc nm (case pcType of (PrdCnsType PrdRep _) -> Prd; (PrdCnsType CnsRep _) -> Cns) i) | n <- ns]

-- XDataRefined
insertXtors dc pol (Just (tyn,argVars)) pk@(MkPolyKind args _) xtors = do
  let vars = map (\(x,_,_) -> x) args
  newNode <- newNodeM
  let skolems = zip argVars (repeat newNode)
  let xtorLabel = singleNodeLabelXtor pol dc (Just (tyn, vars)) (S.fromList (sigToLabel <$> xtors)) pk
  insertNode newNode xtorLabel 
  --ns <- local (extendEnv rep) (insertType ty)
  mapM_ (\(MkXtorSig xt ctxt) -> mapM_ (insertCtxt newNode xt skolems) (enumerate ctxt)) xtors
  return newNode
  where 
    insertCtxt :: Node -> XtorName -> [(SkolemTVar,Node)]-> (Int, PrdCnsType pol) -> TTA ()
    insertCtxt newNode nm skolems (i,pcType) = do 
      ns <- local (extendEnv skolems) (insertPCType pcType)
      insertEdges [(newNode, n, EdgeSymbol dc nm (case pcType of (PrdCnsType PrdRep _) -> Prd; (PrdCnsType CnsRep _) -> Cns) i) | n <- ns]
    extendEnv :: [(SkolemTVar, Node)] -> LookupEnv -> LookupEnv
    extendEnv skolems (LookupEnv tSkolemVars tRecVars) = LookupEnv (foldr (\(sk,node) mp -> M.insert sk (node,node) mp) tSkolemVars skolems) tRecVars 


insertPCType :: PrdCnsType pol -> TTA [Node]
insertPCType (PrdCnsType _ ty) = insertType ty

insertVariantType :: VariantType pol -> TTA ([Node], Variance)
insertVariantType (CovariantType ty) = do
  ns <- insertType ty
  pure (ns, Covariant)
insertVariantType (ContravariantType ty) = do
  ns <- insertType ty
  pure (ns, Contravariant)

insertType :: Typ pol -> TTA [Node]
insertType (TySkolemVar _ rep _ tv) = pure <$> lookupTVar rep tv
insertType (TyUniVar loc _ _ tv) = throwAutomatonError loc  [ "Could not insert type into automaton."
                                                            , "The unification variable:"
                                                            , "    " <> tv.unUniTVar
                                                            , "should not appear at this point in the program."
                                                            ]
insertType (TyRecVar _ rep _ tv) = pure <$> lookupTRecVar rep tv
insertType (TyTop _ knd) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Neg knd)
  pure $ pure newNode
insertType (TyBot _ knd) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Pos knd)
  pure $ pure newNode
insertType (TyUnion _ knd ty1 ty2) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Pos knd)
  ty1s <- insertType ty1
  ty2s <- insertType ty2
  pure $ newNode : (ty1s ++ ty2s)
insertType (TyInter _ knd ty1 ty2) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Neg knd)
  ty1s <- insertType ty1
  ty2s <- insertType ty2
  pure $ newNode : (ty1s ++ ty2s)
insertType (TyRec _ rep rv ty) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel pol (getKind ty))
  let extendEnv PosRep (LookupEnv tSkolemVars tRecVars) = LookupEnv tSkolemVars (M.insert rv (Just newNode, Nothing) tRecVars) 
      extendEnv NegRep (LookupEnv tSkolemVars tRecVars) = LookupEnv tSkolemVars (M.insert rv (Nothing, Just newNode) tRecVars)
  ns <- local (extendEnv rep) (insertType ty)
  addPredecessorsOf newNode ns
  return $ newNode : ns
insertType (TyData _  polrep eo xtors)             = pure <$> insertXtors CST.Data   (polarityRepToPol polrep) Nothing (MkPolyKind [] eo) xtors
insertType (TyCodata _ polrep eo  xtors)           = pure <$> insertXtors CST.Codata (polarityRepToPol polrep) Nothing (MkPolyKind [] eo) xtors
insertType (TyDataRefined _ polrep pk argVars mtn xtors)   = pure <$> insertXtors CST.Data   (polarityRepToPol polrep) (Just (mtn,argVars)) pk xtors
insertType (TyCodataRefined _ polrep pk argVars mtn xtors) = pure <$> insertXtors CST.Codata (polarityRepToPol polrep) (Just (mtn,argVars)) pk xtors
insertType (TySyn _ _ _ ty) = insertType ty

insertType (TyApp _ _ _ ty tyn args) = do 
  argNodes <- mapM insertVariantType args
  tyNodes <-  insertType ty
  insertEdges (concatMap (\(i,(ns,variance)) -> [(tyNode, n, TypeArgEdge tyn variance i) | tyNode <- tyNodes, n <- ns]) $ enumerate (NE.toList argNodes))
  return tyNodes

insertType (TyNominal _ rep pk@(MkPolyKind args _) tn) = do
  let pol = polarityRepToPol rep 
  let vars = map (\(x,_,_) -> x) args
  newNode <- newNodeM
  insertNode newNode (singleNodeLabelNominal pol (tn,vars) pk )
  return $ pure newNode
insertType (TyNominal loc _ knd tyn) = throwAutomatonError loc ["Nominal Type " <> ppPrint tyn <> " can't have kind " <> ppPrint knd]

insertType (TyI64 _ rep) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol I64)
  return $ pure newNode
insertType (TyF64 _ rep) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol F64)
  return $ pure newNode
insertType (TyChar _ rep) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol PChar)
  return $ pure newNode
insertType (TyString _ rep) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol PString)
  return $ pure newNode
insertType (TyFlipPol _ _) =
  throwAutomatonError defaultLoc ["Tried to insert TyFlipPol into type automaton"]

addPredecessorsOf :: Node -> [Node] -> TTA ()
addPredecessorsOf n ns = modifyGraph addPreds
  where
    addPreds :: TypeGr -> TypeGr
    addPreds gr = G.insEdges [ (pred,succ,edge) | (pred,edge) <- G.lpre gr n, succ <- ns ] gr
      

--------------------------------------------------------------------------
--
--------------------------------------------------------------------------


-- turns a type into a type automaton with prescribed start polarity.
typeToAut :: TypeScheme pol -> Either (NonEmpty Error) (TypeAut pol)
typeToAut ts = do 
  (start, aut) <- runTypeAutTvars ts.ts_vars (insertType ts.ts_monotype)
  return TypeAut { ta_pol = getPolarity ts.ts_monotype
                 , ta_starts = start
                 , ta_core = aut
                 }
