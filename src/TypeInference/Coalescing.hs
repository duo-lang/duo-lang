module TypeInference.Coalescing ( coalesce ) where

import Control.Monad.State
import Control.Monad.Reader
import Data.Bifunctor ( Bifunctor(second) )
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text qualified as T

import Syntax.Common.TypesPol
import Syntax.Common
import TypeInference.Constraints
import Utils

---------------------------------------------------------------------------------
-- Coalescing
---------------------------------------------------------------------------------

type CoalesceState  = (Int, Map (TVar, Polarity) TVar)
type CoalesceReader = (SolverResult, Set (TVar, Polarity))

type CoalesceM  a = ReaderT CoalesceReader (State CoalesceState) a

runCoalesceM :: SolverResult ->  CoalesceM a -> a
runCoalesceM res m = evalState (runReaderT m (res,S.empty)) (0, M.empty)

freshRecVar :: CoalesceM TVar
freshRecVar = do
    (i,_) <- get
    modify (\(i,m) -> (i + 1, m))
    return (MkTVar (T.pack $ "rr" ++ show i)) -- Use "rr" so that they don't clash.

inProcess :: (TVar, Polarity) -> CoalesceM Bool
inProcess ptv = do
    inp <- asks snd
    return $ ptv `S.member` inp

getVariableState :: TVar -> CoalesceM VariableState
getVariableState tv = do
    mp <- asks (tvarSolution . fst)
    case M.lookup tv mp of
      Nothing -> error ("Not in variable states: " ++ show (unTVar tv))
      Just vs -> return vs

getRecVar :: (TVar, Polarity) -> CoalesceM TVar
getRecVar ptv = do
    mp <- gets snd
    case M.lookup ptv mp of
      Nothing -> do
          recVar <- freshRecVar
          modify (second (M.insert ptv recVar))
          return recVar
      Just tv -> return tv

coalesce :: SolverResult -> Bisubstitution
coalesce result@MkSolverResult { tvarSolution } = MkBisubstitution (M.fromList xs)
    where
        res = M.keys tvarSolution
        f tvar = (tvar, ( runCoalesceM result $ coalesceType $ TyVar defaultLoc PosRep Nothing tvar
                        , runCoalesceM result $ coalesceType $ TyVar defaultLoc NegRep Nothing tvar))
        xs = f <$> res

coalesceType :: Typ pol -> CoalesceM (Typ pol)
coalesceType (TyVar _ PosRep _ tv) = do
    isInProcess <- inProcess (tv, Pos)
    if isInProcess
        then do
            recVar <- getRecVar (tv, Pos)
            return (TyVar defaultLoc PosRep Nothing recVar)
        else do
            VariableState { vst_lowerbounds } <- getVariableState tv
            let f (i,m) = ( i, S.insert (tv, Pos) m)
            lbs' <- local f $ sequence $ coalesceType <$> vst_lowerbounds
            recVarMap <- gets snd
            case M.lookup (tv, Pos) recVarMap of
                Nothing     -> return $                                 mkUnion defaultLoc Nothing (TyVar defaultLoc PosRep Nothing tv:lbs')
                Just recVar -> return $ TyRec defaultLoc PosRep recVar (mkUnion defaultLoc Nothing (TyVar defaultLoc PosRep Nothing tv:lbs'))
coalesceType (TyVar _ NegRep _ tv) = do
    isInProcess <- inProcess (tv, Neg)
    if isInProcess
        then do
            recVar <- getRecVar (tv, Neg)
            return (TyVar defaultLoc NegRep Nothing recVar)
        else do
            VariableState { vst_upperbounds } <- getVariableState tv
            let f (i,m) = ( i, S.insert (tv, Neg) m)
            ubs' <- local f $ sequence $ coalesceType <$> vst_upperbounds
            recVarMap <- gets snd
            case M.lookup (tv, Neg) recVarMap of
                Nothing     -> return $                                 mkInter defaultLoc Nothing (TyVar defaultLoc NegRep Nothing tv:ubs')
                Just recVar -> return $ TyRec defaultLoc NegRep recVar (mkInter defaultLoc Nothing (TyVar defaultLoc NegRep Nothing tv:ubs'))
coalesceType (TyData loc rep xtors) = do
    xtors' <- sequence $ coalesceXtor <$> xtors
    return (TyData loc rep xtors')
coalesceType (TyCodata loc rep xtors) = do
    xtors' <- sequence $ coalesceXtor <$> xtors
    return (TyCodata loc rep xtors')
coalesceType (TyDataRefined loc rep tn xtors) = do
    xtors' <- sequence $ coalesceXtor <$> xtors
    return (TyDataRefined loc rep tn xtors')
coalesceType (TyCodataRefined loc rep tn xtors) = do
    xtors' <- sequence $ coalesceXtor <$> xtors
    return (TyCodataRefined loc rep tn xtors')
coalesceType (TyNominal loc rep kind tn args) = do
    args' <- sequence $ coalesceVariantType <$> args
    return $ TyNominal loc rep kind tn args'
coalesceType (TySyn _loc _rep _nm ty) = coalesceType ty
coalesceType (TyTop loc knd) =
    pure (TyTop loc knd)
coalesceType (TyBot loc knd) =
    pure (TyBot loc knd)
coalesceType (TyUnion loc knd ty1 ty2) = do
    ty1' <- coalesceType ty1
    ty2' <- coalesceType ty2
    pure (TyUnion loc knd ty1' ty2')
coalesceType (TyInter loc knd ty1 ty2) = do
    ty1' <- coalesceType ty1
    ty2' <- coalesceType ty2
    pure (TyInter loc knd ty1' ty2')
coalesceType (TyRec loc PosRep tv ty) = do
    modify (second (M.insert (tv, Pos) tv))
    let f = second (S.insert (tv, Pos))
    ty' <- local f $ coalesceType ty
    return $ TyRec loc PosRep tv ty'
coalesceType (TyRec loc NegRep tv ty) = do
    modify (second (M.insert (tv, Neg) tv))
    let f = second (S.insert (tv, Neg))
    ty' <- local f $ coalesceType ty
    return $ TyRec loc NegRep tv ty'
coalesceType t@TyPrim {} = return t
coalesceType (TyFlipPol _ _) = error "Tried to coalesce TyFlipPol"


coalesceVariantType :: VariantType pol -> CoalesceM (VariantType pol)
coalesceVariantType (CovariantType ty) = CovariantType <$> coalesceType ty
coalesceVariantType (ContravariantType ty) = ContravariantType <$> coalesceType ty

coalescePrdCnsType :: PrdCnsType pol -> CoalesceM (PrdCnsType pol)
coalescePrdCnsType (PrdCnsType rep ty) = PrdCnsType rep <$> coalesceType ty

coalesceCtxt :: LinearContext pol -> CoalesceM (LinearContext pol)
coalesceCtxt = mapM coalescePrdCnsType

coalesceXtor :: XtorSig pol -> CoalesceM (XtorSig pol)
coalesceXtor (MkXtorSig name ctxt) = do
    ctxt' <- coalesceCtxt ctxt
    return $ MkXtorSig name ctxt'

