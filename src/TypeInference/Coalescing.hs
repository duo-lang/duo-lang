module TypeInference.Coalescing ( coalesce ) where

import Control.Monad.State
import Control.Monad.Reader
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text qualified as T

import Syntax.Kinds
import Syntax.Types
import Syntax.Zonking ( Bisubstitution(..), zonkType)
import TypeInference.Constraints

---------------------------------------------------------------------------------
-- Coalescing Monad
---------------------------------------------------------------------------------

data CoalesceState  = MkCoalesceState
  { varGen :: !Int
  , recursiveMap ::  !(Map (TVar, Polarity) (TVar, Kind))
  }

initialCoalesceState :: CoalesceState
initialCoalesceState = MkCoalesceState 0 M.empty

data CoalesceReader = MkCoalesceReader
  { solverResult :: !SolverResult
  , inProcessSet :: !(Set (TVar, Polarity))
  }

type CoalesceM  a = ReaderT CoalesceReader (State CoalesceState) a

runCoalesceM :: SolverResult ->  CoalesceM a -> a
runCoalesceM res m = evalState (runReaderT m (MkCoalesceReader res S.empty)) initialCoalesceState

---------------------------------------------------------------------------------
-- Helper Functions
---------------------------------------------------------------------------------

freshRecVar :: CoalesceM TVar
freshRecVar = do
    i <- gets varGen
    modify (\s@MkCoalesceState { varGen } -> s { varGen = varGen + 1 })
    return (MkTVar (T.pack $ "rr" ++ show i)) -- Use "rr" so that they don't clash.


inProcess :: (TVar, Polarity) -> CoalesceM Bool
inProcess ptv = do
    inp <- asks inProcessSet
    return $ ptv `S.member` inp

getVariableState :: TVar -> CoalesceM VariableState
getVariableState tv = do
    mp <- asks (tvarSolution . solverResult)
    case M.lookup tv mp of
      Nothing -> error ("Not in variable states: " ++ show (tvar_name tv))
      Just vs -> return vs

lookupKind :: TVar -> CoalesceM Kind
lookupKind tv = do
    state <- getVariableState tv
    return (vst_kind state)

getRecVar :: (TVar, Polarity) -> CoalesceM (TVar, Kind)
getRecVar ptv = do
    mp <- gets recursiveMap
    case M.lookup ptv mp of
      Nothing -> do
          recVar <- freshRecVar
          kind <- lookupKind (fst ptv)
          modify (\s@MkCoalesceState { recursiveMap } -> s { recursiveMap = M.insert ptv (recVar,kind) recursiveMap })
          return (recVar, kind)
      Just tv -> return tv
 
---------------------------------------------------------------------------------
-- Coalescing
---------------------------------------------------------------------------------

coalesce :: SolverResult -> Bisubstitution
coalesce result@(MkSolverResult { tvarSolution, kvarSolution }) = MkBisubstitution (M.fromList xs) kvarSolution
    where
        res = M.toList tvarSolution
        f :: (TVar, VariableState) -> (TVar, (Typ Pos, Typ Neg))
        f (tvar,state) = (tvar, ( zonkType (MkBisubstitution mempty kvarSolution) $ runCoalesceM result $ coalesceType $ TyVar PosRep (Just (vst_kind state)) tvar
                                , zonkType (MkBisubstitution mempty kvarSolution) $ runCoalesceM result $ coalesceType $ TyVar NegRep (Just (vst_kind state)) tvar))
        xs = f <$> res

coalesceType :: Typ pol -> CoalesceM (Typ pol)
coalesceType (TyVar PosRep _ tv) = do
    isInProcess <- inProcess (tv, Pos)
    if isInProcess
        then do
            (recVar,kind) <- getRecVar (tv, Pos)
            return (TyVar PosRep (Just kind) recVar)
        else do
            VariableState { vst_lowerbounds, vst_kind } <- getVariableState tv
            let f r@MkCoalesceReader { inProcessSet } = r { inProcessSet = S.insert (tv, Pos) inProcessSet }
            lbs' <- local f $ sequence $ coalesceType <$> vst_lowerbounds
            recVarMap <- gets recursiveMap
            case M.lookup (tv, Pos) recVarMap of
                Nothing         -> return $                      TySet PosRep (Just vst_kind) (TyVar PosRep (Just vst_kind) tv:lbs')
                Just (recVar,_) -> return $ TyRec PosRep recVar (TySet PosRep (Just vst_kind) (TyVar PosRep (Just vst_kind) tv:lbs'))
coalesceType (TyVar NegRep _ tv) = do
    isInProcess <- inProcess (tv, Neg)
    if isInProcess
        then do
            (recVar,kind) <- getRecVar (tv, Neg)
            return (TyVar NegRep (Just kind) recVar)
        else do
            VariableState { vst_upperbounds, vst_kind } <- getVariableState tv
            let f r@MkCoalesceReader { inProcessSet } = r { inProcessSet = S.insert (tv, Neg) inProcessSet }
            ubs' <- local f $ sequence $ coalesceType <$> vst_upperbounds
            recVarMap <- gets recursiveMap
            case M.lookup (tv, Neg) recVarMap of
                Nothing         -> return $                      TySet NegRep (Just vst_kind) (TyVar NegRep (Just vst_kind) tv:ubs')
                Just (recVar,_) -> return $ TyRec NegRep recVar (TySet NegRep (Just vst_kind) (TyVar NegRep (Just vst_kind) tv:ubs'))
coalesceType (TyData rep tn xtors) = do
    xtors' <- sequence $ coalesceXtor <$> xtors
    return (TyData rep tn xtors')
coalesceType (TyCodata rep tn xtors) = do
    xtors' <- sequence $ coalesceXtor <$> xtors
    return (TyCodata rep tn xtors')
coalesceType (TyNominal rep kind tn) =
    return $ TyNominal rep kind tn
coalesceType (TySet rep kind tys) = do
    tys' <- sequence $ coalesceType <$> tys
    return (TySet rep kind tys')
coalesceType (TyRec PosRep tv ty) = do
    modify (\s@MkCoalesceState { recursiveMap } -> s { recursiveMap =  M.insert (tv, Pos) (tv, getKind ty) recursiveMap })
    let f r@MkCoalesceReader { inProcessSet } = r { inProcessSet = S.insert (tv, Pos) inProcessSet }
    ty' <- local f $ coalesceType ty
    return $ TyRec PosRep tv ty'
coalesceType (TyRec NegRep tv ty) = do
    modify (\s@MkCoalesceState { recursiveMap } -> s { recursiveMap =  M.insert (tv, Neg) (tv, getKind ty) recursiveMap })
    let f r@MkCoalesceReader { inProcessSet } = r { inProcessSet = S.insert (tv, Neg) inProcessSet }
    ty' <- local f $ coalesceType ty
    return $ TyRec NegRep tv ty'

coalescePrdCnsType :: PrdCnsType pol -> CoalesceM (PrdCnsType pol)
coalescePrdCnsType (PrdCnsType rep ty) = PrdCnsType rep <$> coalesceType ty

coalesceCtxt :: LinearContext pol -> CoalesceM (LinearContext pol)
coalesceCtxt = mapM coalescePrdCnsType

coalesceXtor :: XtorSig pol -> CoalesceM (XtorSig pol)
coalesceXtor (MkXtorSig name ctxt) = do
    ctxt' <- coalesceCtxt ctxt
    return $ MkXtorSig name ctxt'

