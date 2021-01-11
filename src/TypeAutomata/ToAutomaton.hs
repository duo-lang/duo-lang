module TypeAutomata.ToAutomaton ( typeToAut, typeToAutPol ) where

import Syntax.Terms
import Syntax.Types
import Syntax.TypeGraph
import Utils
import TypeAutomata.FlowAnalysis
import TypeAutomata.Determinize (determinize, removeEpsilonEdges)
import TypeAutomata.Minimize (minimize)


import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.Void
import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Data.Graph.Inductive.Graph



--------------------------------------------------------------------------
-- Target types -> Type automata
--------------------------------------------------------------------------
data LookupEnv = LookupEnv { rvarEnv :: Map (PrdCns, TVar) Node
                           , tvarEnv :: Map TVar (Node, Node)
                           }
type TypeToAutM a = StateT TypeAutEps (ReaderT LookupEnv (Except Error)) a

runTypeAut :: TypeAutEps -> LookupEnv -> TypeToAutM a -> Either Error (a, TypeAutEps)
runTypeAut graph lookupEnv f = runExcept (runReaderT (runStateT f graph) lookupEnv)

modifyGraph :: (TypeGrEps -> TypeGrEps) -> TypeToAutM ()
modifyGraph f = modify (\(aut@TypeAut { ta_gr }) -> aut { ta_gr = f ta_gr })

createInitialFromTypeScheme :: [TVar] -> (TypeAutEps, LookupEnv)
createInitialFromTypeScheme tvars =
  let
    initGr = mkGraph [(2 * i + offset, (pol, emptyHeadCons)) | i <- [0..length tvars - 1], pol <- [Prd, Cns],
                                                                 let offset = case pol of {Prd -> 0; Cns -> 1}] []
    initAut = TypeAut { ta_gr = initGr
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

typeToAutM :: PrdCns -> TargetType -> TypeToAutM Node
typeToAutM _ (TyUVar v _) = absurd v
typeToAutM pol (TyTVar () Normal tv) = do
  tvarEnv <- asks tvarEnv
  case M.lookup tv tvarEnv of
    Just (i,j) -> return $ case pol of {Prd -> i; Cns -> j}
    Nothing -> throwError $ OtherError $ "unknown free type variable: " ++ (tvar_name tv)
typeToAutM pol (TyTVar () Recursive rv) = do
  rvarEnv <- asks rvarEnv
  case M.lookup (pol, rv) rvarEnv of
    Just i -> return i
    Nothing -> throwError $ OtherError $ "covariance rule violated: " ++ (tvar_name rv)
typeToAutM Prd (TySet () Union tys) = do
  newNode <- newNodeM
  modifyGraph (insNode (newNode, (Prd, emptyHeadCons)))
  ns <- mapM (typeToAutM Prd) tys
  modifyGraph (insEdges [(newNode, n, Nothing) | n <- ns])
  return newNode
typeToAutM Cns (TySet () Union _) = throwError $ OtherError "typeToAutM: type has wrong polarity."
typeToAutM Cns (TySet () Inter tys) = do
  newNode <- newNodeM
  modifyGraph (insNode (newNode, (Cns, emptyHeadCons)))
  ns <- mapM (typeToAutM Cns) tys
  modifyGraph (insEdges [(newNode, n, Nothing) | n <- ns])
  return newNode
typeToAutM Prd (TySet () Inter _) = throwError $ OtherError "typeToAutM: type has wrong polarity."
typeToAutM pol (TyRec () rv ty) = do
  newNode <- newNodeM
  modifyGraph (insNode (newNode, (pol, emptyHeadCons)))
  n <- local (\(LookupEnv rvars tvars) -> LookupEnv ((M.insert (pol, rv) newNode) rvars) tvars) (typeToAutM pol ty)
  modifyGraph (insEdge (newNode, n, Nothing))
  return newNode
typeToAutM pol (TySimple s xtors) = do
  newNode <- newNodeM
  let nl = (pol, singleHeadCons s (S.fromList (map sig_name xtors)))
  modifyGraph (insNode (newNode,nl))
  edges <- forM xtors $ \(MkXtorSig xt (Twice prdTypes cnsTypes)) -> do
    prdNodes <- mapM (typeToAutM (applyVariance s Prd pol)) prdTypes
    cnsNodes <- mapM (typeToAutM (applyVariance s Cns pol)) cnsTypes
    return $ [(newNode, n, Just (EdgeSymbol s xt Prd i)) | i <- [0..length prdNodes - 1], let n = prdNodes !! i] ++
             [(newNode, n, Just (EdgeSymbol s xt Cns i)) | i <- [0..length cnsNodes - 1], let n = cnsNodes !! i]
  modifyGraph (insEdges (concat edges))
  return newNode
typeToAutM pol (TyNominal tn) = do
  newNode <- newNodeM
  let nl = (pol, emptyHeadCons { hc_nominal = S.singleton tn })
  modifyGraph (insNode (newNode, nl))
  return newNode
