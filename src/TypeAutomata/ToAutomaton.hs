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
import Syntax.Common
import Syntax.Common.TypesPol
import TypeAutomata.Definition
    ( TypeAutEps,
      TypeAut'(..),
      TypeGrEps,
      TypeAutCore(..),
      FlowEdge,
      EdgeLabelEpsilon,
      EdgeLabel(..),
      NodeLabel(..),
      XtorLabel(..),
      emptyNodeLabel,
      singleNodeLabel )
import Utils ( enumerate, defaultLoc )
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
-- mapped to a pair `(Just n, Just m)`
newtype LookupEnv = LookupEnv { tvarEnv :: Map SkolemTVar (Maybe Node, Maybe Node) }

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
createNodes :: [SkolemTVar] -> [(SkolemTVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)]
createNodes tvars = createNode <$> createPairs tvars
  where
    createNode :: (SkolemTVar, Node, Node) -> (SkolemTVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)
    createNode (tv, posNode, negNode) = (tv, (posNode, emptyNodeLabel Pos), (negNode, emptyNodeLabel Neg), (negNode, posNode))

    createPairs :: [SkolemTVar] -> [(SkolemTVar,Node,Node)]
    createPairs tvs = (\i -> (tvs !! i, 2 * i, 2 * i + 1)) <$> [0..length tvs - 1]


initialize :: [SkolemTVar] -> (TypeAutCore EdgeLabelEpsilon, LookupEnv)
initialize tvars =
  let
    nodes = createNodes tvars
    initAut = TypeAutCore
              { ta_gr = G.mkGraph ([pos | (_,pos,_,_) <- nodes] ++ [neg | (_,_,neg,_) <- nodes]) []
              , ta_flowEdges = [ flowEdge | (_,_,_,flowEdge) <- nodes]
              }
    lookupEnv = LookupEnv { tvarEnv = M.fromList [(tv, (Just posNode,Just negNode)) | (tv,(posNode,_),(negNode,_),_) <- nodes]
                          }
  in
    (initAut, lookupEnv)

-- | An alternative to `runTypeAut` where the initial state is constructed from a list of Tvars.
runTypeAutTvars :: [SkolemTVar]
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
  tvarEnv <- asks tvarEnv
  case M.lookup tv tvarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The type variable:"
                                              , "    " <> unSkolemTVar tv
                                              , "is not available in the automaton."
                                              ]
    Just (Nothing,_) -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                                       , "The type variable:"
                                                       , "    " <> unSkolemTVar tv
                                                       , "exists only at negative polarity."
                                                       ]
    Just (Just pos,_) -> return pos
lookupTVar NegRep tv = do
  tvarEnv <- asks tvarEnv
  case M.lookup tv tvarEnv of
    Nothing -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                              , "The type variable:"
                                              , "    " <> unSkolemTVar tv
                                              , "is not available in the automaton."
                                              ]
    Just (_,Nothing) -> throwAutomatonError defaultLoc [ "Could not insert type into automaton."
                                                       , "The type variable:"
                                                       , "    " <> unSkolemTVar tv
                                                       , "exists only at positive polarity."
                                                       ]
    Just (_,Just neg) -> return neg



--------------------------------------------------------------------------
-- Inserting a type into an automaton
--------------------------------------------------------------------------

sigToLabel :: XtorSig pol -> XtorLabel
sigToLabel (MkXtorSig name ctxt) = MkXtorLabel name (linearContextToArity ctxt)

insertXtors :: DataCodata -> Polarity -> Maybe RnTypeName -> [XtorSig pol] -> TTA Node
insertXtors dc pol mtn xtors = do
  newNode <- newNodeM
  insertNode newNode (singleNodeLabel pol dc mtn (S.fromList (sigToLabel <$> xtors)))
  forM_ xtors $ \(MkXtorSig xt ctxt) -> do
    forM_ (enumerate ctxt) $ \(i, pcType) -> do
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

insertType (TyTop _ _) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Neg)
  pure newNode
insertType (TyBot _ _) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Pos)
  pure newNode
insertType (TyUnion _ _ ty1 ty2) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Pos)
  ty1' <- insertType ty1
  ty2' <- insertType ty2
  insertEdges [(newNode, ty1', EpsilonEdge ()), (newNode, ty2', EpsilonEdge ())]
  pure newNode
insertType (TyInter _ _ ty1 ty2) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel Neg)
  ty1' <- insertType ty1
  ty2' <- insertType ty2
  insertEdges [(newNode, ty1', EpsilonEdge ()), (newNode, ty2', EpsilonEdge ())]
  pure newNode
insertType (TyRec _ rep rv ty) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel pol)
  let extendEnv PosRep (LookupEnv tvars) = LookupEnv $ M.insert rv (Just newNode, Nothing) tvars
      extendEnv NegRep (LookupEnv tvars) = LookupEnv $ M.insert rv (Nothing, Just newNode) tvars
  n <- local (extendEnv rep) (insertType ty)
  insertEdges [(newNode, n, EpsilonEdge ())]
  return newNode
insertType (TyData _ polrep xtors)   = insertXtors Data   (polarityRepToPol polrep) Nothing xtors
insertType (TyCodata _ polrep xtors) = insertXtors Codata (polarityRepToPol polrep) Nothing xtors
insertType (TyDataRefined _ polrep mtn xtors)   = insertXtors Data   (polarityRepToPol polrep) (Just mtn) xtors
insertType (TyCodataRefined _ polrep mtn xtors) = insertXtors Codata (polarityRepToPol polrep) (Just mtn) xtors
insertType (TySyn _ _ _ ty) = insertType ty
insertType (TyNominal _ rep _ tn args) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode ((emptyNodeLabel pol) { nl_nominal = S.singleton (tn, toVariance <$> args) })
  argNodes <- forM args insertVariantType
  insertEdges ((\(i, (n, variance)) -> (newNode, n, TypeArgEdge tn variance i)) <$> enumerate argNodes)
  return newNode
insertType (TyPrim _ rep pt) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode ((emptyNodeLabel pol) { nl_primitive = S.singleton pt })
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
