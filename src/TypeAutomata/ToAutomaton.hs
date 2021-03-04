module TypeAutomata.ToAutomaton ( typeToAut, solverStateToTypeAut) where

import Syntax.CommonTerm (PrdCns(..))
import Syntax.Types
import Syntax.TypeAutomaton
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
type TypeToAutM pol a = StateT (TypeAutEps pol) (ReaderT LookupEnv (Except Error)) a

runTypeAut :: TypeAutEps pol -> LookupEnv -> TypeToAutM pol a -> Either Error (a, TypeAutEps pol)
runTypeAut graph lookupEnv f = runExcept (runReaderT (runStateT f graph) lookupEnv)

--------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------

modifyGraph :: (TypeGrEps -> TypeGrEps) -> TypeToAutM pol ()
modifyGraph f = modify (\(aut@TypeAut { ta_gr }) -> aut { ta_gr = f ta_gr })

insertNode :: Node -> NodeLabel -> TypeToAutM pol ()
insertNode node nodelabel = modifyGraph (G.insNode (node, nodelabel))

insertEdges :: [(Node,Node,EdgeLabelEpsilon)] -> TypeToAutM pol ()
insertEdges edges = modifyGraph (G.insEdges edges)

newNodeM :: TypeToAutM pol Node
newNodeM = do
  graph <- gets ta_gr
  pure $ (head . G.newNodes 1) graph

lookupTVar :: TVar -> TypeToAutM pol (Node, Node)
lookupTVar tv = do
  tvarEnv <- asks tvarEnv
  case M.lookup tv tvarEnv of
    Just pair -> return pair
    Nothing -> throwError $ OtherError $ "unknown free type variable: " ++ (tvar_name tv)
--------------------------------------------------------------------------
-- Inserting a type into an automaton
--------------------------------------------------------------------------

insertType :: Polarity -> Typ pol -> TypeToAutM pol' Node
insertType pol (TyVar _ Normal tv) = do
  (i,j) <- lookupTVar tv
  return $ case pol of {Pos -> i; Neg -> j}
insertType pol (TyVar _ Recursive rv) = do
  rvarEnv <- asks rvarEnv
  case M.lookup (pol, rv) rvarEnv of
    Just i -> return i
    Nothing -> throwError $ OtherError $ "covariance rule violated: " ++ (tvar_name rv)
insertType Pos (TySet PosRep tys) = do
  newNode <- newNodeM
  insertNode newNode (emptyHeadCons Pos)
  ns <- mapM (insertType Pos) tys
  insertEdges [(newNode, n, EpsilonEdge ()) | n <- ns]
  return newNode
insertType Neg (TySet PosRep _) = throwError $ OtherError "insertType: type has wrong polarity."
insertType Neg (TySet NegRep tys) = do
  newNode <- newNodeM
  insertNode newNode (emptyHeadCons Neg)
  ns <- mapM (insertType Neg) tys
  insertEdges [(newNode, n, EpsilonEdge ()) | n <- ns]
  return newNode
insertType Pos (TySet NegRep _) = throwError $ OtherError "insertType: type has wrong polarity."
insertType pol (TyRec _ rv ty) = do
  newNode <- newNodeM
  insertNode newNode (emptyHeadCons pol)
  n <- local (\(LookupEnv rvars tvars) -> LookupEnv ((M.insert (pol, rv) newNode) rvars) tvars) (insertType pol ty)
  insertEdges [(newNode, n, EpsilonEdge ())]
  return newNode
insertType pol (TyStructural _ DataRep xtors) = do
  newNode <- newNodeM
  insertNode newNode (singleHeadCons pol Data (S.fromList (map sig_name xtors)))
  forM_ xtors $ \(MkXtorSig xt (MkTypArgs prdTypes cnsTypes)) -> do
    forM_ (enumerate prdTypes) $ \(i, prdType) -> do
      prdNode <- insertType pol prdType
      insertEdges [(newNode, prdNode, EdgeSymbol Data xt Prd i)]
    forM_ (enumerate cnsTypes) $ \(j, cnsType) -> do
      cnsNode <- insertType (flipPol pol) cnsType
      insertEdges [(newNode, cnsNode, EdgeSymbol Data xt Cns j)]
  return newNode
insertType pol (TyStructural _ CodataRep xtors) = do
  newNode <- newNodeM
  insertNode newNode (singleHeadCons pol Codata (S.fromList (map sig_name xtors)))
  forM_ xtors $ \(MkXtorSig xt (MkTypArgs prdTypes cnsTypes)) -> do
    forM_ (enumerate prdTypes) $ \(i, prdType) -> do
      prdNode <- insertType (flipPol pol) prdType
      insertEdges [(newNode, prdNode, EdgeSymbol Codata xt Prd i)]
    forM_ (enumerate cnsTypes) $ \(j, cnsType) -> do
      cnsNode <- insertType pol cnsType
      insertEdges [(newNode, cnsNode, EdgeSymbol Codata xt Cns j)]
  return newNode
insertType pol (TyNominal _ tn) = do
  newNode <- newNodeM
  insertNode newNode ((emptyHeadCons pol) { hc_nominal = S.singleton tn })
  return newNode

createInitialFromTypeScheme :: PolarityRep pol -> [TVar] -> (TypeAutEps pol, LookupEnv)
createInitialFromTypeScheme rep tvars =
  let
    nodes = [(2 * i + offset, emptyHeadCons pol) | i <- [0..length tvars - 1], pol <- [Pos, Neg],
                                                                 let offset = case pol of {Pos -> 0; Neg -> 1}]
    initAut = TypeAut { ta_pol = rep
                      , ta_gr = G.mkGraph nodes []
                      , ta_starts = []
                      , ta_flowEdges = [(2 * i + 1, 2 * i) | i <- [0..length tvars - 1]]
                      }
    lookupEnv = LookupEnv { rvarEnv = M.empty
                          , tvarEnv = M.fromList [(tv, (2*i,2*i+1)) | i <- [0..length tvars - 1], let tv = tvars !! i]
                          }
  in
    (initAut, lookupEnv)


-- turns a type into a type automaton with prescribed start polarity (throws an error if the type doesn't match the polarity)
typeToAut :: TypeScheme pol -> Either Error (TypeAutDet pol)
typeToAut (TypeScheme tvars ty) = do
  let (initAut, lookupEnv) = createInitialFromTypeScheme (getPolarity ty) tvars
  (start, aut) <- runTypeAut initAut lookupEnv (insertType (case (getPolarity ty) of PosRep -> Pos; NegRep -> Neg) ty)
  let newaut = aut { ta_starts = [start] }
  pure $ (minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges) newaut

-- | Turns the output of the constraint solver into an automaton by using epsilon-edges to represent lower and upper bounds
insertEpsilonEdges :: SolverResult -> TypeToAutM pol ()
insertEpsilonEdges solverResult =
  forM_ (M.toList solverResult) $ \(tv, vstate) -> do
    (i,j) <- lookupTVar tv
    forM_ (vst_lowerbounds vstate) $ \ty -> do
      node <- insertType Pos ty
      insertEdges [(i, node, EpsilonEdge ())]
    forM_ (vst_upperbounds vstate) $ \ty -> do
      node <- insertType Neg ty
      insertEdges [(j, node, EpsilonEdge ())]

solverStateToTypeAut :: SolverResult -> PolarityRep pol -> Typ pol -> Either Error (TypeAut pol)
solverStateToTypeAut solverResult pol ty = do
  let (initAut, lookupEnv) = createInitialFromTypeScheme pol (M.keys solverResult)
  ((),aut0) <- runTypeAut initAut lookupEnv (insertEpsilonEdges solverResult)
  (start, aut1) <- runTypeAut aut0 lookupEnv (insertType (case pol of PosRep -> Pos; NegRep -> Neg) ty)
  return $ (removeIslands . removeEpsilonEdges) (aut1 { ta_starts = [start] })
