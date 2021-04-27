module TypeAutomata.ToAutomaton ( typeToAut, solverStateToTypeAut) where

import Syntax.CommonTerm (PrdCns(..))
import Syntax.Types
import TypeAutomata.Definition
import Utils
import TypeAutomata.RemoveAdmissible (removeAdmissableFlowEdges)
import TypeAutomata.Determinize (determinize, removeEpsilonEdges, removeIslands)
import TypeAutomata.Minimize (minimize)

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Data.Graph.Inductive.Graph (Node)
import qualified Data.Graph.Inductive.Graph as G

--------------------------------------------------------------------------
-- The Monad
--------------------------------------------------------------------------

data LookupEnv = LookupEnv { tvarEnv :: Map TVar (Maybe Node, Maybe Node) }

type TypeToAutM a = StateT (TypeAutCore EdgeLabelEpsilon) (ReaderT LookupEnv (Except Error)) a

runTypeAut :: TypeAutCore EdgeLabelEpsilon -> LookupEnv -> TypeToAutM a -> Either Error (a, TypeAutCore EdgeLabelEpsilon)
runTypeAut graph lookupEnv f = runExcept (runReaderT (runStateT f graph) lookupEnv)

--------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------

throwAutomatonError :: [String] -> TypeToAutM a
throwAutomatonError msg = throwError $ TypeAutomatonError (unlines msg)

modifyGraph :: (TypeGrEps -> TypeGrEps) -> TypeToAutM ()
modifyGraph f = modify (\(aut@TypeAutCore { ta_gr }) -> aut { ta_gr = f ta_gr })

insertNode :: Node -> NodeLabel -> TypeToAutM ()
insertNode node nodelabel = modifyGraph (G.insNode (node, nodelabel))

insertEdges :: [(Node,Node,EdgeLabelEpsilon)] -> TypeToAutM ()
insertEdges edges = modifyGraph (G.insEdges edges)

newNodeM :: TypeToAutM Node
newNodeM = do
  graph <- gets ta_gr
  pure $ (head . G.newNodes 1) graph

lookupTVar :: PolarityRep pol -> TVar -> TypeToAutM Node
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

insertXtors :: DataCodata -> Polarity -> [XtorSig pol] -> TypeToAutM Node
insertXtors dc pol xtors = do
  newNode <- newNodeM
  insertNode newNode (singleNodeLabel pol dc (S.fromList (sigToLabel <$> xtors)))
  forM_ xtors $ \(MkXtorSig xt (MkTypArgs prdTypes cnsTypes)) -> do
    forM_ (enumerate prdTypes) $ \(i, prdType) -> do
      prdNode <- insertType prdType
      insertEdges [(newNode, prdNode, EdgeSymbol dc xt Prd i)]
    forM_ (enumerate cnsTypes) $ \(j, cnsType) -> do
      cnsNode <- insertType cnsType
      insertEdges [(newNode, cnsNode, EdgeSymbol dc xt Cns j)]
  return newNode

insertType :: Typ pol -> TypeToAutM Node
insertType (TyVar rep tv) = lookupTVar rep tv
insertType (TySet rep tys) = do
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel (polarityRepToPol rep))
  ns <- mapM insertType tys
  insertEdges [(newNode, n, EpsilonEdge ()) | n <- ns]
  return newNode
insertType (TyRec rep rv ty) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode (emptyNodeLabel pol)
  let extendEnv PosRep (LookupEnv tvars) = LookupEnv $ M.insert rv (Just newNode, Nothing) tvars
      extendEnv NegRep (LookupEnv tvars) = LookupEnv $ M.insert rv (Nothing, Just newNode) tvars
  n <- local (extendEnv rep) (insertType ty)
  insertEdges [(newNode, n, EpsilonEdge ())]
  return newNode
insertType (TyData polrep xtors)   = insertXtors Data   (polarityRepToPol polrep) xtors
insertType (TyCodata polrep xtors) = insertXtors Codata (polarityRepToPol polrep) xtors
insertType (TyNominal rep tn) = do
  let pol = polarityRepToPol rep
  newNode <- newNodeM
  insertNode newNode ((emptyNodeLabel pol) { nl_nominal = S.singleton tn })
  return newNode


--------------------------------------------------------------------------
-- 
--------------------------------------------------------------------------

-- | Every type variable is mapped to a pair of nodes.
createNodes :: [TVar] -> [(TVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)]
createNodes tvars = createNode <$> (createPairs tvars)
  where
    createNode :: (TVar, Node, Node) -> (TVar, (Node, NodeLabel), (Node, NodeLabel), FlowEdge)
    createNode (tv, posNode, negNode) = (tv, (posNode, emptyNodeLabel Pos), (negNode, emptyNodeLabel Neg), (posNode, negNode))

    createPairs :: [TVar] -> [(TVar,Node,Node)]
    createPairs tvs = (\i -> (tvs !! i, 2 * i, 2 * i + 1)) <$> [0..length tvs - 1]


createInitialFromTypeScheme :: [TVar] -> (TypeAutCore EdgeLabelEpsilon, LookupEnv)
createInitialFromTypeScheme tvars =
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


-- turns a type into a type automaton with prescribed start polarity.
typeToAut :: TypeScheme pol -> Either Error (TypeAutDet pol)
typeToAut (TypeScheme tvars ty) = do
  let (initAut, lookupEnv) = createInitialFromTypeScheme tvars
  (start, aut) <- runTypeAut initAut lookupEnv (insertType ty)
  let newaut = TypeAut { ta_pol = getPolarity ty
                       , ta_starts = [start]
                       , ta_core = aut
                       }
  pure $ (minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges) newaut

-- | Turns the output of the constraint solver into an automaton by using epsilon-edges to represent lower and upper bounds
insertEpsilonEdges :: SolverResult -> TypeToAutM ()
insertEpsilonEdges solverResult =
  forM_ (M.toList solverResult) $ \(tv, vstate) -> do
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
  let (initAut, lookupEnv) = createInitialFromTypeScheme (M.keys solverResult)
  ((),aut0) <- runTypeAut initAut lookupEnv (insertEpsilonEdges solverResult)
  (start, aut1) <- runTypeAut aut0 lookupEnv (insertType ty)
  let newAut = TypeAut { ta_starts = [start], ta_pol = pol, ta_core = aut1 }
  return $ (removeIslands . removeEpsilonEdges) newAut
