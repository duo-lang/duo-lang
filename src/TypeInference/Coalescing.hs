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

type CoalesceState  = (Int, Map (SkolemTVar, Polarity) SkolemTVar)
type CoalesceReader = (SolverResult, Set (UniTVar, Polarity))

type CoalesceM  a = ReaderT CoalesceReader (State CoalesceState) a

runCoalesceM :: SolverResult ->  CoalesceM a -> a
runCoalesceM res m = evalState (runReaderT m (res,S.empty)) (0, M.empty)

freshRecVar :: CoalesceM SkolemTVar
freshRecVar = do
    (i,_) <- get
    modify (\(i,m) -> (i + 1, m))
    return (MkSkolemTVar (T.pack $ "rr" ++ show i)) -- Use "rr" so that they don't clash.

inProcess :: (SkolemTVar, Polarity) -> CoalesceM Bool
inProcess ptv = do
    inp <- gets snd 
    return $ ptv `M.member` inp

getVariableState :: UniTVar -> CoalesceM VariableState
getVariableState tv = do
    mp <- asks (tvarSolution . fst)
    case M.lookup tv mp of
      Nothing -> error ("Not in variable states: " ++ show (unUniTVar tv))
      Just vs -> return vs

getRecVar :: (SkolemTVar, Polarity) -> CoalesceM SkolemTVar
getRecVar ptv = do
    mp <- gets snd
    case M.lookup ptv mp of
      Nothing -> do
          recVar <- freshRecVar
          modify (second (M.insert ptv recVar))
          return recVar
      Just tv -> return tv

coalesce :: SolverResult -> Bisubstitution
coalesce result@MkSolverResult { tvarSolution } = MkBisubstitution (M.fromList xs) M.empty
    where
        res = M.keys tvarSolution
        f tvar = (tvar, ( runCoalesceM result $ coalesceType $ UniTyVar defaultLoc PosRep Nothing tvar
                        , runCoalesceM result $ coalesceType $ UniTyVar defaultLoc NegRep Nothing tvar))
        xs = f <$> res

coalesceType :: Typ pol -> CoalesceM (Typ pol)
coalesceType (UniTyVar _ PosRep _ tv) = do
    VariableState { vst_lowerbounds } <- getVariableState tv
    let f (i,m) = ( i, S.insert (tv, Pos) m)
    lbs' <- local f $ sequence $ coalesceType <$> vst_lowerbounds
    return $ mkUnion defaultLoc Nothing (UniTyVar defaultLoc PosRep Nothing tv:lbs')
coalesceType (UniTyVar _ NegRep _ tv) = do
    VariableState { vst_upperbounds } <- getVariableState tv
    let f (i,m) = ( i, S.insert (tv, Neg) m)
    ubs' <- local f $ sequence $ coalesceType <$> vst_upperbounds
    return $  mkInter defaultLoc Nothing (UniTyVar defaultLoc NegRep Nothing tv:ubs')
coalesceType (SkolemTyVar _ NegRep _ tv) = do
    isInProcess <- inProcess (tv, Neg)
    if isInProcess
        then do
            recVar <- getRecVar (tv, Neg)
            return (SkolemTyVar defaultLoc NegRep Nothing recVar)
        else do
            --VariableState { vst_upperbounds } <- getVariableState tv
            --let f (i,m) = ( i, S.insert (tv, Neg) m)
            --ubs' <- local f $ sequence $ coalesceType <$> vst_upperbounds
            recVarMap <- gets snd
            case M.lookup (tv, Neg) recVarMap of
                Nothing -> error ("Skolem Variable " ++ show tv ++ " not found in Recursive Variables" )
                Just (MkSkolemTVar recVar) -> return $ TyRec defaultLoc NegRep (MkSkolemTVar recVar) (mkInter defaultLoc Nothing [SkolemTyVar defaultLoc NegRep Nothing tv]) -- :ubs'))
coalesceType (SkolemTyVar _ PosRep _ tv) = do
    isInProcess <- inProcess (tv, Pos)
    if isInProcess
        then do
            recVar <- getRecVar (tv, Pos)
            return (SkolemTyVar defaultLoc PosRep Nothing recVar)
        else do
            --VariableState { vst_lowerbounds } <- getVariableState tv
            --let f (i,m) = ( i, S.insert (tv, Pos) m)
            --lbs' <- local f $ sequence $ coalesceType <$> vst_lowerbounds
            recVarMap <- gets snd
            case M.lookup (tv, Pos) recVarMap of
                Nothing  -> error  ("Skolem Variable " ++ show tv ++ " not found in Recursive Variables" )
                Just (MkSkolemTVar recVar) -> return $ TyRec defaultLoc PosRep (MkSkolemTVar recVar) (mkUnion defaultLoc Nothing [SkolemTyVar defaultLoc PosRep Nothing tv]) -- :lbs'))

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
    --let f = second (S.insert (tv, Pos))
    --ty' <- local f $ coalesceType ty
    return $ TyRec loc PosRep tv  ty -- '
coalesceType (TyRec loc NegRep tv ty) = do
    modify (second (M.insert (tv, Neg) tv))
    --let f = second (S.insert (tv, Neg))
    --ty' <- local f $ coalesceType ty
    return $ TyRec loc NegRep tv ty -- '
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

