module TypeAutomata.ToAutomaton ( typeToAut ) where


import Control.Monad ( forM_ )
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
import Syntax.CommonTerm (PrdCns(..))
import Syntax.Types
import Syntax.Kinds
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
createNodes :: [(TVar,Kind)] -> [(TVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)]
createNodes tvars = createNode <$> (createPairs tvars)
  where
    createNode :: (TVar, Kind, Node, Node) -> (TVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)
    createNode (tv, kind, posNode, negNode) = (tv, (posNode, emptyNodeLabel Pos kind), (negNode, emptyNodeLabel Neg kind), (negNode, posNode))

    createPairs :: [(TVar,Kind)] -> [(TVar,Kind, Node,Node)]
    createPairs tvs = (\i -> (fst $ tvs !! i, snd $ tvs !! i, 2 * i, 2 * i + 1)) <$> [0..length tvs - 1]


initialize :: [(TVar,Kind)] -> (TypeAutCore EdgeLabelEpsilon, LookupEnv)
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
runTypeAutTvars :: [(TVar,Kind)]
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
                                   , "    " <> tvar_name tv
                                   , "is not available in the automaton."
                                   ]
    Just (Nothing,_) -> throwAutomatonError $ [ "Could not insert type into automaton."
                                              , "The type variable:"
                                              , "    " <> tvar_name tv
                                              , "exists, but not with the correct polarity."
                                              ]
    Just (Just pos,_) -> return pos


lookupTVar NegRep tv = do
  tvarEnv <- asks tvarEnv
  case M.lookup tv tvarEnv of
    Nothing -> throwAutomatonError [ "Could not insert type into automaton."
                                   , "The type variable:"
                                   , "    " <> tvar_name tv
                                   , "is not available in the automaton."
                                   ]
    Just (_,Nothing) -> throwAutomatonError $ [ "Could not insert type into automaton."
                                              , "The type variable:"
                                              , "    " <> tvar_name tv
                                              , "exists, but not with the correct polarity."
                                              ]
    Just (_,Just neg) -> return neg



--------------------------------------------------------------------------
-- Inserting a type into an automaton
--------------------------------------------------------------------------


linearContextToArity :: LinearContext pol -> [PrdCns]
linearContextToArity = map f
  where
    f (PrdType _) = Prd
    f (CnsType _) = Cns

sigToLabel :: XtorSig pol -> XtorLabel
sigToLabel (MkXtorSig name ctxt) = MkXtorLabel name (linearContextToArity ctxt)

insertXtors :: DataCodata -> Polarity -> Maybe TypeName -> [XtorSig pol] -> TTA Node
insertXtors dc pol mtn xtors = do
  newNode <- newNodeM
  insertNode newNode (singleNodeLabel pol (case dc of Data -> MonoKind CBV; Codata -> MonoKind CBN) dc mtn (S.fromList (sigToLabel <$> xtors)))
  forM_ xtors $ \(MkXtorSig xt ctxt) -> do
    forM_ (enumerate ctxt) $ \(i, pcType) -> do
      node <- insertPCType pcType
      insertEdges [(newNode, node, EdgeSymbol dc xt (case pcType of (PrdType _)-> Prd; (CnsType _) -> Cns) i)]
  return newNode

insertPCType :: PrdCnsType pol -> TTA Node
insertPCType (PrdType ty) = insertType ty
insertPCType (CnsType ty) = insertType ty

insertType :: Typ pol -> TTA Node
insertType (TyVar rep _ tv) = lookupTVar rep tv
insertType (TySet rep (Just kind) tys) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel (polarityRepToPol rep) kind)
  ns <- mapM insertType tys
  insertEdges [(newNode, n, EpsilonEdge ()) | n <- ns]
  return newNode
insertType (TySet _ Nothing _) = throwAutomatonError ["Tried to insert TySet which was not kind-annotated"]
insertType (TyRec rep rv ty) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel pol (getKind ty))
  let extendEnv PosRep (LookupEnv tvars) = LookupEnv $ M.insert rv (Just newNode, Nothing) tvars
      extendEnv NegRep (LookupEnv tvars) = LookupEnv $ M.insert rv (Nothing, Just newNode) tvars
  n <- local (extendEnv rep) (insertType ty)
  insertEdges [(newNode, n, EpsilonEdge ())]
  return newNode
insertType (TyData polrep mtn xtors)   = insertXtors Data   (polarityRepToPol polrep) mtn xtors
insertType (TyCodata polrep mtn xtors) = insertXtors Codata (polarityRepToPol polrep) mtn xtors
insertType (TyNominal rep (Just kind) tn) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode ((emptyNodeLabel pol kind) { nl_nominal = S.singleton tn })
  return newNode
insertType (TyNominal _ Nothing _) = throwAutomatonError ["Tried to insert TyNominal which was not kind-annotated"]

--------------------------------------------------------------------------
--
--------------------------------------------------------------------------


-- turns a type into a type automaton with prescribed start polarity.
typeToAut :: TypeScheme pol -> Either Error (TypeAutEps pol)
typeToAut (TypeScheme tvars ty) = do
  (start, aut) <- runTypeAutTvars tvars (insertType ty) --  TODO Change definition of TypeScheme
  return TypeAut { ta_pol = getPolarity ty
                 , ta_starts = [start]
                 , ta_core = aut
                 }
