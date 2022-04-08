module TypeAutomata.ToAutomaton ( typeToAut ) where


import Control.Monad.Except ( runExcept, Except )
import Control.Monad.Reader
    ( ReaderT(..), asks, MonadReader(..) )
import Control.Monad.State
    ( StateT(..), gets, modify )
import Data.Graph.Inductive.Graph (Node)
import Data.Graph.Inductive.Graph qualified as G
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set qualified as S

import Errors ( Error, throwAutomatonError )
import Pretty.Types ()
import Syntax.Common
import Syntax.RST.Types
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
-- Unification variables exist both positively and negatively. They are therefore
-- mapped to a pair `(Just n, Just m)`
data LookupEnv = LookupEnv { tvarEnv :: Map TVar (Maybe Node, Maybe Node) }

type TTA a = StateT (TypeAutCore EdgeLabelEpsilon) (ReaderT LookupEnv (Except Error)) a

runTypeAut :: TypeAutCore EdgeLabelEpsilon
           -- ^ The initial TypeAutomaton to start the computation.
           -> LookupEnv
           -- ^ The initial lookup environment.
           -> TTA a
           -- ^ The computation to run.
           -> Either Error (a, TypeAutCore EdgeLabelEpsilon)
runTypeAut graph lookupEnv f = runExcept (runReaderT (runStateT f graph) lookupEnv)


-- | Every type variable is mapped to a pair of nodes.
createNodes :: [TVar] -> [(TVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)]
createNodes tvars = createNode <$> (createPairs tvars)
  where
    createNode :: (TVar, Node, Node) -> (TVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)
    createNode (tv, posNode, negNode) = (tv, (posNode, emptyNodeLabel Pos), (negNode, emptyNodeLabel Neg), (negNode, posNode))

    createPairs :: [TVar] -> [(TVar,Node,Node)]
    createPairs tvs = (\i -> (tvs !! i, 2 * i, 2 * i + 1)) <$> [0..length tvs - 1]


initialize :: [TVar] -> (TypeAutCore EdgeLabelEpsilon, LookupEnv)
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
runTypeAutTvars :: [TVar]
                -> TTA a
                -> Either Error (a, TypeAutCore EdgeLabelEpsilon)
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

lookupTVar :: PolarityRep pol -> TVar -> TTA Node
lookupTVar PosRep tv = do
  tvarEnv <- asks tvarEnv
  case M.lookup tv tvarEnv of
    Nothing -> throwAutomatonError [ "Could not insert type into automaton."
                                   , "The type variable:"
                                   , "    " <> unTVar tv
                                   , "is not available in the automaton."
                                   ]
    Just (Nothing,_) -> throwAutomatonError $ [ "Could not insert type into automaton."
                                              , "The type variable:"
                                              , "    " <> unTVar tv
                                              , "exists, but not with the correct polarity."
                                              ]
    Just (Just pos,_) -> return pos


lookupTVar NegRep tv = do
  tvarEnv <- asks tvarEnv
  case M.lookup tv tvarEnv of
    Nothing -> throwAutomatonError [ "Could not insert type into automaton."
                                   , "The type variable:"
                                   , "    " <> unTVar tv
                                   , "is not available in the automaton."
                                   ]
    Just (_,Nothing) -> throwAutomatonError $ [ "Could not insert type into automaton."
                                              , "The type variable:"
                                              , "    " <> unTVar tv
                                              , "exists, but not with the correct polarity."
                                              ]
    Just (_,Just neg) -> return neg



--------------------------------------------------------------------------
-- Inserting a type into an automaton
--------------------------------------------------------------------------

sigToLabel :: XtorSig pol -> XtorLabel
sigToLabel (MkXtorSig name ctxt) = MkXtorLabel name (linearContextToArity ctxt)

insertXtors :: DataCodata -> Polarity -> Maybe TypeName -> [XtorSig pol] -> TTA Node
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
insertType (TyVar _ rep _ tv) = lookupTVar rep tv
insertType (TySet _ rep _ tys) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel (polarityRepToPol rep))
  ns <- mapM insertType tys
  insertEdges [(newNode, n, EpsilonEdge ()) | n <- ns]
  return newNode
insertType (TyRec _ rep rv ty) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel pol)
  let extendEnv PosRep (LookupEnv tvars) = LookupEnv $ M.insert rv (Just newNode, Nothing) tvars
      extendEnv NegRep (LookupEnv tvars) = LookupEnv $ M.insert rv (Nothing, Just newNode) tvars
  n <- local (extendEnv rep) (insertType ty)
  insertEdges [(newNode, n, EpsilonEdge ())]
  return newNode
insertType (TyData _ polrep mtn xtors)   = insertXtors Data   (polarityRepToPol polrep) mtn xtors
insertType (TyCodata _ polrep mtn xtors) = insertXtors Codata (polarityRepToPol polrep) mtn xtors
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

--------------------------------------------------------------------------
--
--------------------------------------------------------------------------


-- turns a type into a type automaton with prescribed start polarity.
typeToAut :: TypeScheme pol -> Either Error (TypeAutEps pol)
typeToAut (TypeScheme { ts_vars, ts_monotype }) = do
  (start, aut) <- runTypeAutTvars ts_vars (insertType ts_monotype)
  return TypeAut { ta_pol = getPolarity ts_monotype
                 , ta_starts = [start]
                 , ta_core = aut
                 }
