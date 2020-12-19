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

import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Data.Graph.Inductive.Graph



--------------------------------------------------------------------------
-- Target types -> Type automata
--------------------------------------------------------------------------

type RVarEnv = Map (PrdCns, TVar) Node
type TVarEnv = Map TVar (Node, Node)
type TypeToAutM a = StateT TypeGrEps (ReaderT RVarEnv (ReaderT TVarEnv (Except String))) a

-- turns a type into a type automaton with prescribed start polarity (throws an error if the type doesn't match the polarity)
typeToAutPol :: PrdCns -> TypeScheme -> Either String TypeAutDet
typeToAutPol pol (TypeScheme tvars ty) =
  let
    tvarMap = M.fromList [(tv, (2*i,2*i+1)) | i <- [0..length tvars - 1], let tv = tvars !! i]
    initGr = mkGraph [(2 * i + offset, (pol, emptyHeadCons)) | i <- [0..length tvars - 1], pol <- [Prd, Cns],
                                                               let offset = case pol of {Prd -> 0; Cns -> 1}] []
    flowEdges = [(2 * i + 1, 2 * i) | i <- [0..length tvars - 1]]
  in
    case runExcept (runReaderT (runReaderT (runStateT (typeToAutM pol ty) initGr) M.empty) tvarMap) of
      Right (start, gr) ->
        let
          aut = TypeAut { ta_gr = gr, ta_starts = [start], ta_flowEdges = flowEdges }
        in
          Right $ (minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges) aut
      Left err -> Left err

-- tries both polarites (positive by default). Throws an error if the type is not polar.
typeToAut :: TypeScheme -> Either String TypeAutDet
typeToAut ty = (typeToAutPol Prd ty) <> (typeToAutPol Cns ty)

typeToAutM :: PrdCns -> TargetType -> TypeToAutM Node
typeToAutM pol (TTyVar Normal tv) = do
  tvarEnv <- lift $ lift ask
  case M.lookup tv tvarEnv of
    Just (i,j) -> return $ case pol of {Prd -> i; Cns -> j}
    Nothing -> throwError $ "unknown free type variable: " ++ (tvar_name tv)
typeToAutM pol (TTyVar Rec rv) = do
  rvarEnv <- ask
  case M.lookup (pol, rv) rvarEnv of
    Just i -> return i
    Nothing -> throwError $ "covariance rule violated: " ++ (tvar_name rv)
typeToAutM Prd (TTySet Union tys) = do
  newNode <- head . newNodes 1 <$> get
  modify (insNode (newNode, (Prd, emptyHeadCons)))
  ns <- mapM (typeToAutM Prd) tys
  modify (insEdges [(newNode, n, Nothing) | n <- ns])
  return newNode
typeToAutM Cns (TTySet Union _) = throwError "typeToAutM: type has wrong polarity."
typeToAutM Cns (TTySet Inter tys) = do
  newNode <- head . newNodes 1 <$> get
  modify (insNode (newNode, (Cns, emptyHeadCons)))
  ns <- mapM (typeToAutM Cns) tys
  modify (insEdges [(newNode, n, Nothing) | n <- ns])
  return newNode
typeToAutM Prd (TTySet Inter _) = throwError "typeToAutM: type has wrong polarity."
typeToAutM pol (TTyRec rv ty) = do
  newNode <- head . newNodes 1 <$> get
  modify (insNode (newNode, (pol, emptyHeadCons)))
  n <- local (M.insert (pol, rv) newNode) (typeToAutM pol ty)
  modify (insEdge (newNode, n, Nothing))
  return newNode
typeToAutM pol (TTySimple s xtors) = do
  newNode <- head . newNodes 1 <$> get
  let nl = (pol, singleHeadCons s (S.fromList (map sig_name xtors)))
  modify (insNode (newNode,nl))
  edges <- forM xtors $ \(MkXtorSig xt (Twice prdTypes cnsTypes)) -> do
    prdNodes <- mapM (typeToAutM (applyVariance s Prd pol)) prdTypes
    cnsNodes <- mapM (typeToAutM (applyVariance s Cns pol)) cnsTypes
    return $ [(newNode, n, Just (EdgeSymbol s xt Prd i)) | i <- [0..length prdNodes - 1], let n = prdNodes !! i] ++
             [(newNode, n, Just (EdgeSymbol s xt Cns i)) | i <- [0..length cnsNodes - 1], let n = cnsNodes !! i]
  modify (insEdges (concat edges))
  return newNode
typeToAutM pol (TTyNominal tn) = do
  newNode <- head . newNodes 1 <$> get
  let nl = (pol, emptyHeadCons { hc_nominal = S.singleton tn })
  modify (insNode (newNode, nl))
  return newNode
