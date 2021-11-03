module TypeAutomata.ToAutomaton ( typeToAut, solverStateToTypeAut) where

import Syntax.CommonTerm (PrdCns(..))
import Syntax.Types
import TypeAutomata.Definition
import Pretty.Types()
import Utils
import Errors
import TypeAutomata.Determinize (determinize)
import TypeAutomata.Minimize (minimize)
import TypeAutomata.RemoveAdmissible (removeAdmissableFlowEdges)
import TypeAutomata.RemoveEpsilon (removeEpsilonEdges)


import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Set as S
import Syntax.Kinds

import Data.Map (Map)
import qualified Data.Map as M

import Data.Graph.Inductive.Graph (Node)
import qualified Data.Graph.Inductive.Graph as G
import TypeAutomata.Lint (lint)

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
    createNode :: (TVar,Kind, Node, Node) -> (TVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)
    createNode (tv, kind, posNode, negNode) = (tv, (posNode, emptyNodeLabel Pos kind), (negNode, emptyNodeLabel Neg kind), (negNode, posNode))

    createPairs :: [(TVar, Kind)] -> [(TVar,Kind, Node,Node)]
    createPairs tvs = (\i -> (fst $ tvs !! i, snd $ tvs !! i,  2 * i, 2 * i + 1)) <$> [0..length tvs - 1]


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


sigToLabel :: XtorSig pol -> XtorLabel
sigToLabel (MkXtorSig name (MkTypArgs prds cnss)) = MkXtorLabel name (length prds) (length cnss)

insertXtors :: DataCodata -> Polarity -> [XtorSig pol] -> TTA Node
insertXtors dc pol xtors = do
  newNode <- newNodeM
  insertNode newNode (singleNodeLabel pol (case dc of Data -> MonoKind CBV; Codata -> MonoKind CBN) dc (S.fromList (sigToLabel <$> xtors)))
  forM_ xtors $ \(MkXtorSig xt (MkTypArgs prdTypes cnsTypes)) -> do
    forM_ (enumerate prdTypes) $ \(i, prdType) -> do
      prdNode <- insertType prdType
      insertEdges [(newNode, prdNode, EdgeSymbol dc xt Prd i)]
    forM_ (enumerate cnsTypes) $ \(j, cnsType) -> do
      cnsNode <- insertType cnsType
      insertEdges [(newNode, cnsNode, EdgeSymbol dc xt Cns j)]
  return newNode

insertType :: Typ pol -> TTA Node
insertType (TyVar rep _ tv) = lookupTVar rep tv
insertType (TySet rep (Just kind) tys) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel (polarityRepToPol rep) kind)
  ns <- mapM insertType tys
  insertEdges [(newNode, n, EpsilonEdge ()) | n <- ns]
  return newNode
insertType (TySet rep Nothing tys) = insertType (TySet rep (Just (MonoKind CBV)) tys) -- HACKY HACKY HACKY!
insertType (TyRec rep rv ty) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel pol undefined)
  let extendEnv PosRep (LookupEnv tvars) = LookupEnv $ M.insert rv (Just newNode, Nothing) tvars
      extendEnv NegRep (LookupEnv tvars) = LookupEnv $ M.insert rv (Nothing, Just newNode) tvars
  n <- local (extendEnv rep) (insertType ty)
  insertEdges [(newNode, n, EpsilonEdge ())]
  return newNode
-- Insert refinement (co)data as structural (co)data for now
insertType (TyData polrep _ xtors)   = insertXtors Data   (polarityRepToPol polrep) xtors
insertType (TyCodata polrep _ xtors) = insertXtors Codata (polarityRepToPol polrep) xtors
insertType (TyNominal rep (Just kind) tn) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode ((emptyNodeLabel pol kind) { nl_nominal = S.singleton tn })
  return newNode
insertType (TyNominal rep Nothing tn) = insertType (TyNominal rep (Just (MonoKind CBV)) tn) -- HACKY HACKY HACKY ! 
-- insertType ty@(TyData _ (Just _) _) = throwAutomatonError ["Cannot insert refinement type " <> ppPrint ty]
-- insertType ty@(TyCodata _ (Just _) _) = throwAutomatonError ["Cannot insert refinement type " <> ppPrint ty]

--------------------------------------------------------------------------
--
--------------------------------------------------------------------------


-- turns a type into a type automaton with prescribed start polarity.
typeToAut :: TypeScheme pol -> Either Error (TypeAutDet pol)
typeToAut (TypeScheme tvars ty) = do
  (start, aut) <- runTypeAutTvars ((\tv -> (tv, MonoKind CBV)) <$> tvars) (insertType ty)
  let newaut = TypeAut { ta_pol = getPolarity ty
                       , ta_starts = [start]
                       , ta_core = aut
                       }
  pure $ (minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges) newaut

-- | Turns the output of the constraint solver into an automaton by using epsilon-edges to represent lower and upper bounds
insertEpsilonEdges :: SolverResult -> TTA ()
insertEpsilonEdges solverResult =
  forM_ (M.toList (tvarSolution solverResult)) $ \(tv, vstate) -> do
    i <- lookupTVar PosRep tv
    j <- lookupTVar NegRep tv
    forM_ (vst_lowerbounds vstate) $ \ty -> do
      node <- insertType ty
      insertEdges [(i, node, EpsilonEdge ())]
    forM_ (vst_upperbounds vstate) $ \ty -> do
      node <- insertType ty
      insertEdges [(j, node, EpsilonEdge ())]

solverStateToTypeAut :: SolverResult -> PolarityRep pol -> Typ pol -> Either Error (TypeAut pol)
solverStateToTypeAut solverResult pol ty = do
  let foo :: [(TVar, Kind)]= (\(tv,vs) -> (tv, vst_kind vs)) <$> M.toList (tvarSolution solverResult)
  (start,aut) <- runTypeAutTvars  foo $ insertEpsilonEdges solverResult >> insertType ty
  let newAut = TypeAut { ta_starts = [start], ta_pol = pol, ta_core = aut }
  lint newAut
  return $ removeEpsilonEdges newAut
