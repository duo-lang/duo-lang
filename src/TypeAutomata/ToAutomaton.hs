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

import Data.Graph.Inductive.Graph



--------------------------------------------------------------------------
-- Target types -> Type automata
--------------------------------------------------------------------------
data LookupEnv = LookupEnv { rvarEnv :: Map (PrdCns, TVar) Node
                           , tvarEnv :: Map TVar (Node, Node)
                           , uvarEnv :: Map (PrdCns, UVar) Node
                           }
type TypeToAutM a = StateT TypeAutEps (ReaderT LookupEnv (Except Error)) a

runTypeAut :: TypeAutEps -> LookupEnv -> TypeToAutM a -> Either Error (a, TypeAutEps)
runTypeAut graph lookupEnv f = runExcept (runReaderT (runStateT f graph) lookupEnv)

modifyGraph :: (TypeGrEps -> TypeGrEps) -> TypeToAutM ()
modifyGraph f = modify (\(aut@TypeAut { ta_gr }) -> aut { ta_gr = f ta_gr })

createInitialFromTypeScheme :: [TVar] -> (TypeAutEps, LookupEnv)
createInitialFromTypeScheme tvars =
  let
    nodes = [(2 * i + offset, (pol, emptyHeadCons)) | i <- [0..length tvars - 1], pol <- [Prd, Cns],
                                                                 let offset = case pol of {Prd -> 0; Cns -> 1}]
    initAut = TypeAut { ta_gr = mkGraph nodes []
                      , ta_starts = []
                      , ta_flowEdges = [(2 * i + 1, 2 * i) | i <- [0..length tvars - 1]]
                      }
    lookupEnv = LookupEnv { rvarEnv = M.empty
                          , tvarEnv = M.fromList [(tv, (2*i,2*i+1)) | i <- [0..length tvars - 1], let tv = tvars !! i]
                          , uvarEnv = M.empty
                          }
  in
    (initAut, lookupEnv)

uvarToNodeId :: UVar -> PrdCns -> Node
uvarToNodeId uv Prd = 2 * uvar_id uv
uvarToNodeId uv Cns  = 2 * uvar_id uv + 1

-- | Creates an initial type automaton from a list of UVars.
mkInitialTypeAut :: [UVar] -> (TypeAutEps, LookupEnv)
mkInitialTypeAut uvs =
  let
    uvNodes = [(uvarToNodeId uv pol, (pol, emptyHeadCons)) | uv <- uvs, pol <- [Prd,Cns]]
    initAut = TypeAut { ta_gr = mkGraph uvNodes []
                      , ta_starts = []
                      , ta_flowEdges = [(uvarToNodeId uv Cns, uvarToNodeId uv Prd) | uv <- uvs]
            }
    lookupEnv = LookupEnv { rvarEnv = M.empty
                          , tvarEnv = M.empty
                          , uvarEnv = undefined
                          }
  in
    (initAut, lookupEnv)


-- turns a type into a type automaton with prescribed start polarity (throws an error if the type doesn't match the polarity)
typeToAutPol :: PrdCns -> TypeScheme -> Either Error TypeAutDet
typeToAutPol pol (TypeScheme tvars ty) = do
  let (initAut, lookupEnv) = createInitialFromTypeScheme tvars
  (start, aut) <- runTypeAut initAut lookupEnv (typeToAutM pol ty)
  let newaut = aut { ta_starts = [start] }
  pure $ (minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges) newaut


-- tries both polarites (positive by default). Throws an error if the type is not polar.
typeToAut :: TypeScheme -> Either Error TypeAutDet
typeToAut ty = (typeToAutPol Prd ty) <> (typeToAutPol Cns ty)


--------------------------------------------------------------------------
-- Type insertion helpers
--------------------------------------------------------------------------

newNodeM :: TypeToAutM Node
newNodeM = do
  graph <- gets ta_gr
  pure $ (head . newNodes 1) graph

typeToAutM :: PrdCns -> Typ a -> TypeToAutM Node
typeToAutM pol (TyUVar _ uv) = return (uvarToNodeId uv pol) -- HACKYHACKY !!!
typeToAutM pol (TyTVar _ Normal tv) = do
  tvarEnv <- asks tvarEnv
  case M.lookup tv tvarEnv of
    Just (i,j) -> return $ case pol of {Prd -> i; Cns -> j}
    Nothing -> throwError $ OtherError $ "unknown free type variable: " ++ (tvar_name tv)
typeToAutM pol (TyTVar _ Recursive rv) = do
  rvarEnv <- asks rvarEnv
  case M.lookup (pol, rv) rvarEnv of
    Just i -> return i
    Nothing -> throwError $ OtherError $ "covariance rule violated: " ++ (tvar_name rv)
typeToAutM Prd (TySet _ Union tys) = do
  newNode <- newNodeM
  modifyGraph (insNode (newNode, (Prd, emptyHeadCons)))
  ns <- mapM (typeToAutM Prd) tys
  modifyGraph (insEdges [(newNode, n, Nothing) | n <- ns])
  return newNode
typeToAutM Cns (TySet _ Union _) = throwError $ OtherError "typeToAutM: type has wrong polarity."
typeToAutM Cns (TySet _ Inter tys) = do
  newNode <- newNodeM
  modifyGraph (insNode (newNode, (Cns, emptyHeadCons)))
  ns <- mapM (typeToAutM Cns) tys
  modifyGraph (insEdges [(newNode, n, Nothing) | n <- ns])
  return newNode
typeToAutM Prd (TySet _ Inter _) = throwError $ OtherError "typeToAutM: type has wrong polarity."
typeToAutM pol (TyRec _ rv ty) = do
  newNode <- newNodeM
  modifyGraph (insNode (newNode, (pol, emptyHeadCons)))
  n <- local (\(LookupEnv rvars tvars uvars) -> LookupEnv ((M.insert (pol, rv) newNode) rvars) tvars uvars) (typeToAutM pol ty)
  modifyGraph (insEdge (newNode, n, Nothing))
  return newNode
typeToAutM pol (TySimple s xtors) = do
  newNode <- newNodeM
  let nl = (pol, singleHeadCons s (S.fromList (map sig_name xtors)))
  modifyGraph (insNode (newNode,nl))
  forM_ xtors $ \(MkXtorSig xt (Twice prdTypes cnsTypes)) -> do
    forM_ (enumerate prdTypes) $ \(i, prdType) -> do
      prdNode <- typeToAutM (applyVariance s Prd pol) prdType
      modifyGraph (insEdge (newNode, prdNode, Just (EdgeSymbol s xt Prd i)))
    forM_ (enumerate cnsTypes) $ \(j, cnsType) -> do
      cnsNode <- typeToAutM (applyVariance s Cns pol) cnsType
      modifyGraph (insEdge (newNode, cnsNode, Just (EdgeSymbol s xt Cns j)))
  return newNode
typeToAutM pol (TyNominal tn) = do
  newNode <- newNodeM
  let nl = (pol, emptyHeadCons { hc_nominal = S.singleton tn })
  modifyGraph (insNode (newNode, nl))
  return newNode


-- | Turns the output of the constraint solver into an automaton by using epsilon-edges to represent lower and upper bounds
insertEpsilonEdges :: SolverResult -> TypeToAutM ()
insertEpsilonEdges solverResult =
  forM_ (M.toList solverResult) $ \(uv, vstate) -> do
    forM_ (vst_lowerbounds vstate) $ \ty -> do
      i <- typeToAutM Prd ty
      modifyGraph (insEdge (uvarToNodeId uv Prd, i, Nothing))
    forM_ (vst_upperbounds vstate) $ \ty -> do
      i <- typeToAutM Cns ty
      modifyGraph (insEdge (uvarToNodeId uv Cns, i, Nothing))

solverStateToTypeAut :: SolverResult -> SimpleType -> PrdCns -> Either Error TypeAut
solverStateToTypeAut solverResult ty pc = do
  let (initAut, lookupEnv) = mkInitialTypeAut (M.keys solverResult)
  ((),aut0) <- runTypeAut initAut lookupEnv (insertEpsilonEdges solverResult)
  (start, aut1) <- runTypeAut aut0 lookupEnv (typeToAutM pc ty)
  return $ (removeIslands . removeEpsilonEdges) (aut1 { ta_starts = [start] })
