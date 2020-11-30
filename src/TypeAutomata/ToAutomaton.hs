module TypeAutomata.ToAutomaton ( typeToAut, typeToAutPol ) where

import Syntax.Terms
import Syntax.Types
import Syntax.TypeGraph
import Utils
import FlowAnalysis

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import qualified Data.Set as S

import Data.Map (Map)
import qualified Data.Map as M

import Data.Graph.Inductive.Graph

import TypeAutomata.Determinize (determinize, removeEpsilonEdges)
import TypeAutomata.Minimize (minimize)


--------------------------------------------------------------------------
-- Target types -> Type automata
--------------------------------------------------------------------------

type RVarEnv = Map (Polarity, RVar) Node
type TVarEnv = Map TVar (Node, Node)
type TypeToAutM a = StateT TypeGrEps (ReaderT RVarEnv (ReaderT TVarEnv (Except String))) a

-- turns a type into a type automaton with prescribed start polarity (throws an error if the type doesn't match the polarity)
typeToAutPol :: Polarity -> TypeScheme -> Either String TypeAutDet
typeToAutPol pol (TypeScheme tvars ty) =
  let
    tvarMap = M.fromList [(tv, (2*i,2*i+1)) | i <- [0..length tvars - 1], let tv = tvars !! i]
    initGr = mkGraph [(2 * i + offset, (pol, emptyHeadCons)) | i <- [0..length tvars - 1], pol <- [Pos, Neg],
                                                               let offset = case pol of {Pos -> 0; Neg -> 1}] []
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
typeToAut ty = case typeToAutPol Pos ty of
  Right res -> Right res
  Left _ -> case typeToAutPol Neg ty of
    Right res -> Right res
    Left err -> Left err

typeToAutM :: Polarity -> TargetType -> TypeToAutM Node
typeToAutM pol (TTyTVar tv) = do
  tvarEnv <- lift $ lift ask
  case M.lookup tv tvarEnv of
    Just (i,j) -> return $ case pol of {Pos -> i; Neg -> j}
    Nothing -> throwError $ "unknown free type variable: " ++ (tvar_name tv)
typeToAutM pol (TTyRVar rv) = do
  rvarEnv <- ask
  case M.lookup (pol, rv) rvarEnv of
    Just i -> return i
    Nothing -> throwError $ "covariance rule violated: " ++ (rvar_name rv)
typeToAutM Pos (TTyUnion tys) = do
  newNode <- head . newNodes 1 <$> get
  modify (insNode (newNode, (Pos, emptyHeadCons)))
  ns <- mapM (typeToAutM Pos) tys
  modify (insEdges [(newNode, n, Nothing) | n <- ns])
  return newNode
typeToAutM Neg (TTyUnion _) = throwError "typeToAutM: type has wrong polarity."
typeToAutM Neg (TTyInter tys) = do
  newNode <- head . newNodes 1 <$> get
  modify (insNode (newNode, (Neg, emptyHeadCons)))
  ns <- mapM (typeToAutM Neg) tys
  modify (insEdges [(newNode, n, Nothing) | n <- ns])
  return newNode
typeToAutM Pos (TTyInter _) = throwError "typeToAutM: type has wrong polarity."
typeToAutM pol (TTyRec rv ty) = do
  newNode <- head . newNodes 1 <$> get
  modify (insNode (newNode, (pol, emptyHeadCons)))
  n <- local (M.insert (pol, rv) newNode) (typeToAutM pol ty)
  modify (insEdge (newNode, n, Nothing))
  return newNode
typeToAutM pol (TTySimple s xtors) = do
  newNode <- head . newNodes 1 <$> get
  let nl = (pol, singleHeadCons s (S.fromList (map fst xtors)))
  modify (insNode (newNode,nl))
  edges <- forM xtors $ \(xt,Twice prdTypes cnsTypes) -> do
    prdNodes <- mapM (typeToAutM (applyVariance s Prd pol)) prdTypes
    cnsNodes <- mapM (typeToAutM (applyVariance s Cns pol)) cnsTypes
    return $ [(newNode, n, Just (EdgeSymbol s xt Prd i)) | i <- [0..length prdNodes - 1], let n = prdNodes !! i] ++
             [(newNode, n, Just (EdgeSymbol s xt Cns i)) | i <- [0..length cnsNodes - 1], let n = cnsNodes !! i]
  modify (insEdges (concat edges))
  return newNode
