module TypeAutomata.ToAutomaton ( typeToAut, typeToAutPol, solverStateToTypeAut) where

import Syntax.CommonTerm (PrdCns(..))
import Syntax.Types
import Syntax.TypeGraph
import Utils
import TypeAutomata.FlowAnalysis
import TypeAutomata.Determinize (determinize, removeEpsilonEdges, removeIslands)
import TypeAutomata.Minimize (minimize)
import TypeInference.SolveConstraints

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

data LookupEnv = LookupEnv { rvarEnv :: Map (Polarity, TVar) Node
                           , tvarEnv :: Map TVar (Node, Node)
                           }
type TypeToAutM a = StateT TypeAutEps (ReaderT LookupEnv (Except Error)) a

runTypeAut :: TypeAutEps -> LookupEnv -> TypeToAutM a -> Either Error (a, TypeAutEps)
runTypeAut graph lookupEnv f = runExcept (runReaderT (runStateT f graph) lookupEnv)

--------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------

modifyGraph :: (TypeGrEps -> TypeGrEps) -> TypeToAutM ()
modifyGraph f = modify (\(aut@TypeAut { ta_gr }) -> aut { ta_gr = f ta_gr })

insertNode :: Node -> NodeLabel -> TypeToAutM ()
insertNode node nodelabel = modifyGraph (G.insNode (node, nodelabel))

insertEdges :: [(Node,Node,EdgeLabelEpsilon)] -> TypeToAutM ()
insertEdges edges = modifyGraph (G.insEdges edges)

newNodeM :: TypeToAutM Node
newNodeM = do
  graph <- gets ta_gr
  pure $ (head . G.newNodes 1) graph

lookupTVar :: TVar -> TypeToAutM (Node, Node)
lookupTVar tv = do
  tvarEnv <- asks tvarEnv
  case M.lookup tv tvarEnv of
    Just pair -> return pair
    Nothing -> throwError $ OtherError $ "unknown free type variable: " ++ (tvar_name tv)
--------------------------------------------------------------------------
-- Inserting a type into an automaton
--------------------------------------------------------------------------

insertType :: Polarity -> Typ pol -> TypeToAutM Node
insertType pol (TyVar _ Normal tv) = do
  (i,j) <- lookupTVar tv
  return $ case pol of {Pos -> i; Neg -> j}
insertType pol (TyVar _ Recursive rv) = do
  rvarEnv <- asks rvarEnv
  case M.lookup (pol, rv) rvarEnv of
    Just i -> return i
    Nothing -> throwError $ OtherError $ "covariance rule violated: " ++ (tvar_name rv)
insertType Pos (TySet Union tys) = do
  newNode <- newNodeM
  insertNode newNode (emptyHeadCons Pos)
  ns <- mapM (insertType Pos) tys
  insertEdges [(newNode, n, EpsilonEdge ()) | n <- ns]
  return newNode
insertType Neg (TySet Union _) = throwError $ OtherError "insertType: type has wrong polarity."
insertType Neg (TySet Inter tys) = do
  newNode <- newNodeM
  insertNode newNode (emptyHeadCons Neg)
  ns <- mapM (insertType Neg) tys
  insertEdges [(newNode, n, EpsilonEdge ()) | n <- ns]
  return newNode
insertType Pos (TySet Inter _) = throwError $ OtherError "insertType: type has wrong polarity."
insertType pol (TyRec _ rv ty) = do
  newNode <- newNodeM
  insertNode newNode (emptyHeadCons pol)
  n <- local (\(LookupEnv rvars tvars) -> LookupEnv ((M.insert (pol, rv) newNode) rvars) tvars) (insertType pol ty)
  insertEdges [(newNode, n, EpsilonEdge ())]
  return newNode
insertType pol (TyStructural _ s xtors) = do
  newNode <- newNodeM
  insertNode newNode (singleHeadCons pol s (S.fromList (map sig_name xtors)))
  forM_ xtors $ \(MkXtorSig xt (MkTypArgs prdTypes cnsTypes)) -> do
    forM_ (enumerate prdTypes) $ \(i, prdType) -> do
      prdNode <- insertType (applyVariance s Pos pol) prdType
      insertEdges [(newNode, prdNode, EdgeSymbol s xt Prd i)]
    forM_ (enumerate cnsTypes) $ \(j, cnsType) -> do
      cnsNode <- insertType (applyVariance s Neg pol) cnsType
      insertEdges [(newNode, cnsNode, EdgeSymbol s xt Cns j)]
  return newNode
insertType pol (TyNominal _ tn) = do
  newNode <- newNodeM
  insertNode newNode ((emptyHeadCons pol) { hc_nominal = S.singleton tn })
  return newNode

createInitialFromTypeScheme :: [TVar] -> (TypeAutEps, LookupEnv)
createInitialFromTypeScheme tvars =
  let
    nodes = [(2 * i + offset, emptyHeadCons pol) | i <- [0..length tvars - 1], pol <- [Pos, Neg],
                                                                 let offset = case pol of {Pos -> 0; Neg -> 1}]
    initAut = TypeAut { ta_gr = G.mkGraph nodes []
                      , ta_starts = []
                      , ta_flowEdges = [(2 * i + 1, 2 * i) | i <- [0..length tvars - 1]]
                      }
    lookupEnv = LookupEnv { rvarEnv = M.empty
                          , tvarEnv = M.fromList [(tv, (2*i,2*i+1)) | i <- [0..length tvars - 1], let tv = tvars !! i]
                          }
  in
    (initAut, lookupEnv)


-- turns a type into a type automaton with prescribed start polarity (throws an error if the type doesn't match the polarity)
typeToAutPol :: Polarity -> TypeScheme Pos -> Either Error TypeAutDet
typeToAutPol pol (TypeScheme tvars ty) = do
  let (initAut, lookupEnv) = createInitialFromTypeScheme tvars
  (start, aut) <- runTypeAut initAut lookupEnv (insertType pol ty)
  let newaut = aut { ta_starts = [start] }
  pure $ (minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges) newaut


-- tries both polarites (positive by default). Throws an error if the type is not polar.
typeToAut :: TypeScheme Pos -> Either Error TypeAutDet
typeToAut ty = (typeToAutPol Pos ty) <> (typeToAutPol Neg ty)


-- | Turns the output of the constraint solver into an automaton by using epsilon-edges to represent lower and upper bounds
insertEpsilonEdges :: SolverResult -> TypeToAutM ()
insertEpsilonEdges solverResult =
  forM_ (M.toList solverResult) $ \(tv, vstate) -> do
    (i,j) <- lookupTVar tv
    forM_ (vst_lowerbounds vstate) $ \ty -> do
      node <- insertType Pos ty
      insertEdges [(i, node, EpsilonEdge ())]
    forM_ (vst_upperbounds vstate) $ \ty -> do
      node <- insertType Neg ty
      insertEdges [(j, node, EpsilonEdge ())]

solverStateToTypeAut :: SolverResult -> Typ Pos -> Polarity -> Either Error TypeAut
solverStateToTypeAut solverResult ty pol = do
  let (initAut, lookupEnv) = createInitialFromTypeScheme (M.keys solverResult)
  ((),aut0) <- runTypeAut initAut lookupEnv (insertEpsilonEdges solverResult)
  (start, aut1) <- runTypeAut aut0 lookupEnv (insertType pol ty)
  return $ (removeIslands . removeEpsilonEdges) (aut1 { ta_starts = [start] })
