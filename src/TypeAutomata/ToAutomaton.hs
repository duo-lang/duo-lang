module TypeAutomata.ToAutomaton ( typeToAut, typeToAutPol, solverStateToTypeAut) where

import Syntax.Terms
import Syntax.Types
import Syntax.TypeGraph
import Utils
import TypeAutomata.FlowAnalysis
import TypeAutomata.Determinize (determinize, removeEpsilonEdges, removeIslands)
import TypeAutomata.Minimize (minimize)
import SolveConstraints

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

data LookupEnv = LookupEnv { rvarEnv :: Map (PrdCns, TVar) Node
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

insertNode :: Node -> PrdCns -> HeadCons -> TypeToAutM ()
insertNode node pol headcons = modifyGraph (G.insNode (node, (pol, headcons)))

insertEdges :: [(Node,Node,Maybe EdgeLabel)] -> TypeToAutM ()
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

insertType :: PrdCns -> Typ a -> TypeToAutM Node
insertType pol (TyVar Normal tv) = do
  (i,j) <- lookupTVar tv
  return $ case pol of {Prd -> i; Cns -> j}
insertType pol (TyVar Recursive rv) = do
  rvarEnv <- asks rvarEnv
  case M.lookup (pol, rv) rvarEnv of
    Just i -> return i
    Nothing -> throwError $ OtherError $ "covariance rule violated: " ++ (tvar_name rv)
insertType Prd (TySet _ Union tys) = do
  newNode <- newNodeM
  insertNode newNode Prd emptyHeadCons
  ns <- mapM (insertType Prd) tys
  insertEdges [(newNode, n, Nothing) | n <- ns]
  return newNode
insertType Cns (TySet _ Union _) = throwError $ OtherError "insertType: type has wrong polarity."
insertType Cns (TySet _ Inter tys) = do
  newNode <- newNodeM
  insertNode newNode Cns emptyHeadCons
  ns <- mapM (insertType Cns) tys
  insertEdges [(newNode, n, Nothing) | n <- ns]
  return newNode
insertType Prd (TySet _ Inter _) = throwError $ OtherError "insertType: type has wrong polarity."
insertType pol (TyRec _ rv ty) = do
  newNode <- newNodeM
  insertNode newNode pol emptyHeadCons
  n <- local (\(LookupEnv rvars tvars) -> LookupEnv ((M.insert (pol, rv) newNode) rvars) tvars) (insertType pol ty)
  insertEdges [(newNode, n, Nothing)]
  return newNode
insertType pol (TySimple s xtors) = do
  newNode <- newNodeM
  insertNode newNode pol (singleHeadCons s (S.fromList (map sig_name xtors)))
  forM_ xtors $ \(MkXtorSig xt (Twice prdTypes cnsTypes)) -> do
    forM_ (enumerate prdTypes) $ \(i, prdType) -> do
      prdNode <- insertType (applyVariance s Prd pol) prdType
      insertEdges [(newNode, prdNode, Just (EdgeSymbol s xt Prd i))]
    forM_ (enumerate cnsTypes) $ \(j, cnsType) -> do
      cnsNode <- insertType (applyVariance s Cns pol) cnsType
      insertEdges [(newNode, cnsNode, Just (EdgeSymbol s xt Cns j))]
  return newNode
insertType pol (TyNominal tn) = do
  newNode <- newNodeM
  insertNode newNode pol (emptyHeadCons { hc_nominal = S.singleton tn })
  return newNode

createInitialFromTypeScheme :: [TVar] -> (TypeAutEps, LookupEnv)
createInitialFromTypeScheme tvars =
  let
    nodes = [(2 * i + offset, (pol, emptyHeadCons)) | i <- [0..length tvars - 1], pol <- [Prd, Cns],
                                                                 let offset = case pol of {Prd -> 0; Cns -> 1}]
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
typeToAutPol :: PrdCns -> TypeScheme -> Either Error TypeAutDet
typeToAutPol pol (TypeScheme tvars ty) = do
  let (initAut, lookupEnv) = createInitialFromTypeScheme tvars
  (start, aut) <- runTypeAut initAut lookupEnv (insertType pol ty)
  let newaut = aut { ta_starts = [start] }
  pure $ (minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges) newaut


-- tries both polarites (positive by default). Throws an error if the type is not polar.
typeToAut :: TypeScheme -> Either Error TypeAutDet
typeToAut ty = (typeToAutPol Prd ty) <> (typeToAutPol Cns ty)


-- | Turns the output of the constraint solver into an automaton by using epsilon-edges to represent lower and upper bounds
insertEpsilonEdges :: SolverResult -> TypeToAutM ()
insertEpsilonEdges solverResult =
  forM_ (M.toList solverResult) $ \(tv, vstate) -> do
    (i,j) <- lookupTVar tv
    forM_ (vst_lowerbounds vstate) $ \ty -> do
      node <- insertType Prd ty
      insertEdges [(i, node, Nothing)]
    forM_ (vst_upperbounds vstate) $ \ty -> do
      node <- insertType Cns ty
      insertEdges [(j, node, Nothing)]

solverStateToTypeAut :: SolverResult -> SimpleType -> PrdCns -> Either Error TypeAut
solverStateToTypeAut solverResult ty pc = do
  let (initAut, lookupEnv) = createInitialFromTypeScheme (M.keys solverResult)
  ((),aut0) <- runTypeAut initAut lookupEnv (insertEpsilonEdges solverResult)
  (start, aut1) <- runTypeAut aut0 lookupEnv (insertType pc ty)
  return $ (removeIslands . removeEpsilonEdges) (aut1 { ta_starts = [start] })
