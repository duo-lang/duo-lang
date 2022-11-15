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
import Data.Set (Set)

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
createNodes :: [KindedSkolem] -> Set ClassName -> [(SkolemTVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)]
createNodes tvars cns = createNode <$> createPairs tvars
  where
    createNode :: (KindedSkolem, Node, Node) -> (SkolemTVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)
    createNode ((tv, mk), posNode, negNode) = (tv, (posNode, emptyNodeLabel Pos mk cns), (negNode, emptyNodeLabel Neg mk cns), (negNode, posNode))

    createPairs :: [KindedSkolem] -> [(KindedSkolem, Node,Node)]
    createPairs tvs = (\i -> (tvs !! i, 2 * i, 2 * i + 1)) <$> [0..length tvs - 1]


initialize :: [KindedSkolem] -> Set ClassName -> (TypeAutCore EdgeLabelEpsilon, LookupEnv)
initialize tvars cns =
  let
    nodes = createNodes tvars cns
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
  let (aut, env) = initialize tvars S.empty
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

insertXtors :: CST.DataCodata -> Polarity -> Maybe RnTypeName -> EvaluationOrder -> [XtorSig pol] -> Set ClassName -> TTA Node
insertXtors dc pol mtn mk xtors cns = do
  newNode <- newNodeM
  insertNode newNode (singleNodeLabel pol dc mtn (S.fromList (sigToLabel <$> xtors)) cns mk)
  forM_ xtors $ \(MkXtorSig xt ctxt) -> do
    forM_ (enumerate ctxt) $ \(i, pcType) -> do
      node <- insertPCType pcType
      insertEdges [(newNode, node, EdgeSymbol dc xt (case pcType of (PrdCnsType PrdRep _)-> Prd; (PrdCnsType CnsRep _) -> Cns) i)]
  return newNode

insertPCType :: PrdCnsType pol -> TTA Node
insertPCType (PrdCnsType _ ty) = insertType ty S.empty

insertVariantType :: VariantType pol -> TTA (Node, Variance)
insertVariantType (CovariantType ty) = do
  node <- insertType ty S.empty
  pure (node, Covariant)
insertVariantType (ContravariantType ty) = do
  node <- insertType ty S.empty
  pure (node, Contravariant)

insertType :: Typ pol -> Set ClassName -> TTA Node
insertType (TySkolemVar _ rep _ tv) _cns = lookupTVar rep tv
insertType (TyUniVar loc _ _ tv) _cns = throwAutomatonError loc  [ "Could not insert type into automaton."
                                                                 , "The unification variable:"
                                                                 , "    " <> unUniTVar tv
                                                                 , "should not appear at this point in the program."
                                                                 ]
insertType (TyRecVar _ rep _ tv) _cns = lookupTRecVar rep tv
insertType (TyTop _ knd) cns = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Neg knd cns)
  pure newNode
insertType (TyBot _ knd) cns = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Pos knd cns)
  pure newNode
insertType (TyUnion _ knd ty1 ty2) cns = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Pos knd cns)
  ty1' <- insertType ty1 cns
  ty2' <- insertType ty2 cns
  insertEdges [(newNode, ty1', EpsilonEdge ()), (newNode, ty2', EpsilonEdge ())]
  pure newNode
insertType (TyInter _ knd ty1 ty2) cns = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Neg knd cns)
  ty1' <- insertType ty1 cns
  ty2' <- insertType ty2 cns
  insertEdges [(newNode, ty1', EpsilonEdge ()), (newNode, ty2', EpsilonEdge ())]
  pure newNode
insertType (TyRec _ rep rv ty) cns = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel pol (getKind ty) cns)
  let extendEnv PosRep (LookupEnv tSkolemVars tRecVars) = LookupEnv tSkolemVars $ M.insert rv (Just newNode, Nothing) tRecVars
      extendEnv NegRep (LookupEnv tSkolemVars tRecVars) = LookupEnv tSkolemVars $ M.insert rv (Nothing, Just newNode) tRecVars
  n <- local (extendEnv rep) (insertType ty cns)
  insertEdges [(newNode, n, EpsilonEdge ())]
  return newNode
insertType (TyData _  polrep (CBox mk) xtors) cns = insertXtors CST.Data (polarityRepToPol polrep) Nothing mk xtors cns
insertType (TyData _ _ mk _) _cns = throwAutomatonError defaultLoc ["Tried to insert TyData into automaton with incorrect kind " <> ppPrint mk]
insertType (TyCodata _ polrep (CBox mk)  xtors) cns = insertXtors CST.Codata (polarityRepToPol polrep) Nothing mk xtors cns
insertType (TyCodata _ _ mk _) _cns = throwAutomatonError defaultLoc ["Tried to insert TyCodata into automaton with incorrect kind " <> ppPrint mk]
insertType (TyDataRefined _ polrep (CBox mk) mtn xtors) cns = insertXtors CST.Data   (polarityRepToPol polrep) (Just mtn) mk xtors cns
insertType (TyDataRefined _ _ mk _ _) _cns = throwAutomatonError defaultLoc ["Tried to insert TyDataRefined into automaton with incorrect kind " <> ppPrint mk]
insertType (TyCodataRefined _ polrep (CBox mk) mtn xtors) cns = insertXtors CST.Codata (polarityRepToPol polrep) (Just mtn) mk xtors cns
insertType (TyCodataRefined _ _ mk _ _) _cns = throwAutomatonError defaultLoc ["Tried to insert TyCodataRefined into automaton with incorrect kind " <> ppPrint mk]
insertType (TySyn _ _ _ ty) cns = insertType ty cns
insertType (TyNominal _ rep mk tn args) cns = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode ((emptyNodeLabel pol mk cns) { nl_nominal = S.singleton (tn, toVariance <$> args) })
  argNodes <- forM args insertVariantType
  insertEdges ((\(i, (n, variance)) -> (newNode, n, TypeArgEdge tn variance i)) <$> enumerate argNodes)
  return newNode
insertType (TyI64 _ rep) _cns = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol I64)
  return newNode
insertType (TyF64 _ rep) _cns = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol F64)
  return newNode
insertType (TyChar _ rep) _cns = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol PChar)
  return newNode
insertType (TyString _ rep) _cns = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (MkPrimitiveNodeLabel pol PString)
  return newNode
insertType (TyFlipPol _ _) _cns =
  throwAutomatonError defaultLoc ["Tried to insert TyFlipPol into type automaton"]

--------------------------------------------------------------------------
--
--------------------------------------------------------------------------


-- turns a type into a type automaton with prescribed start polarity.
typeToAut :: TypeScheme pol -> Either (NonEmpty Error) (TypeAutEps pol)
typeToAut TypeScheme { ts_vars, ts_monotype, ts_constraints } = do
  let cns = S.fromList $ concatMap (\case {TypeClassConstraint cn var -> [cn]; _ -> []}) ts_constraints
  (start, aut) <- runTypeAutTvars ts_vars (insertType ts_monotype cns)
  return TypeAut { ta_pol = getPolarity ts_monotype
                 , ta_starts = [start]
                 , ta_core = aut
                 }
