module TypeInference.Coalescing where

import Control.Monad.State
import Control.Monad.Reader
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text qualified as T

import Syntax.Types
import TypeInference.Constraints

---------------------------------------------------------------------------------
-- Bisubstitution
---------------------------------------------------------------------------------

newtype Bisubstitution = MkBisubstitution { unBisubstitution :: Map TVar (Typ Pos, Typ Neg) }

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
    i <- get
    modify (\(i,m) -> (i + 1, m))
    return (MkTVar (T.pack $ "rr" ++ show i)) -- Use "rr" so that they don't clash.

inProcess :: (TVar, Polarity) -> CoalesceM Bool
inProcess ptv = do
    inp <- asks snd
    return $ ptv `S.member` inp

getVariableState :: TVar -> CoalesceM VariableState
getVariableState tv = do
    mp <- asks fst
    case M.lookup tv mp of
      Nothing -> error ("Not in variable states: " ++ show (tvar_name tv))
      Just vs -> return vs

getRecVar :: (TVar, Polarity) -> CoalesceM TVar
getRecVar ptv = do
    mp <- gets snd
    case M.lookup ptv mp of
      Nothing -> do
          recVar <- freshRecVar
          modify (\(i,m) -> (i,M.insert ptv recVar m))
          return recVar
      Just tv -> return tv
 
coalesce :: SolverResult -> Bisubstitution
coalesce result = MkBisubstitution $ M.fromList xs
    where
        res = M.keys result
        f tvar = (tvar, ( runCoalesceM result $ coalesceType $ TyVar PosRep tvar
                        , runCoalesceM result $ coalesceType $ TyVar NegRep tvar))
        xs = f <$> res

coalesceType :: Typ pol -> CoalesceM (Typ pol)
coalesceType (TyVar PosRep tv) = do
    isInProcess <- inProcess (tv, Pos)
    if isInProcess
        then do
            recVar <- getRecVar (tv, Pos)
            return (TyVar PosRep recVar)
        else do
            VariableState { vst_lowerbounds } <- getVariableState tv
            let f (i,m) = ( i, S.insert (tv, Pos) m)
            lbs' <- local f $ sequence $ coalesceType <$> vst_lowerbounds
            recVarMap <- gets snd
            case M.lookup (tv, Pos) recVarMap of
                Nothing     -> return $                      TySet PosRep (TyVar PosRep tv:lbs')
                Just recVar -> return $ TyRec PosRep recVar (TySet PosRep (TyVar PosRep tv:lbs'))
coalesceType (TyVar NegRep tv) = do
    isInProcess <- inProcess (tv, Neg)
    if isInProcess
        then do
            recVar <- getRecVar (tv, Neg)
            return (TyVar NegRep recVar)
        else do
            VariableState { vst_upperbounds } <- getVariableState tv
            let f (i,m) = ( i, S.insert (tv, Neg) m)
            ubs' <- local f $ sequence $ coalesceType <$> vst_upperbounds
            recVarMap <- gets snd
            case M.lookup (tv, Neg) recVarMap of
                Nothing     -> return $                      TySet NegRep (TyVar NegRep tv:ubs')
                Just recVar -> return $ TyRec NegRep recVar (TySet NegRep (TyVar NegRep tv:ubs'))
coalesceType (TyData rep tn xtors) = do
    xtors' <- sequence $ coalesceXtor <$> xtors
    return (TyData rep tn xtors')
coalesceType (TyCodata rep tn xtors) = do
    xtors' <- sequence $ coalesceXtor <$> xtors
    return (TyCodata rep tn xtors')
coalesceType (TyNominal rep tn) =
    return $ TyNominal rep tn
coalesceType (TySet rep tys) = do
    tys' <- sequence $ coalesceType <$> tys
    return (TySet rep tys')
coalesceType (TyRec PosRep tv ty) = do
    modify (\(i,m) -> (i, M.insert (tv, Pos) tv m))
    let f = (\(x,s) -> (x, S.insert (tv,Pos) s))
    ty' <- local f $ coalesceType ty
    return $ TyRec PosRep tv ty'
coalesceType (TyRec NegRep tv ty) = do
    modify (\(i,m) -> (i, M.insert (tv, Neg) tv m))
    let f = (\(x,s) -> (x, S.insert (tv,Neg) s))
    ty' <- local f $ coalesceType ty
    return $ TyRec NegRep tv ty'

coalescePrdCnsType :: PrdCnsType pol -> CoalesceM (PrdCnsType pol)
coalescePrdCnsType (PrdType ty) = PrdType <$> coalesceType ty
coalescePrdCnsType (CnsType ty) = CnsType <$> coalesceType ty

coalesceCtxt :: LinearContext pol -> CoalesceM (LinearContext pol)
coalesceCtxt = mapM coalescePrdCnsType

coalesceXtor :: XtorSig pol -> CoalesceM (XtorSig pol)
coalesceXtor (MkXtorSig name ctxt) = do
    ctxt' <- coalesceCtxt ctxt
    return $ MkXtorSig name ctxt'

---------------------------------------------------------------------------------
-- Zonking
---------------------------------------------------------------------------------

zonk :: Bisubstitution -> Typ pol -> Typ pol
zonk bisubst ty@(TyVar PosRep tv ) = case M.lookup tv (unBisubstitution bisubst) of
    Nothing -> ty -- Recursive variable!
    Just (tyPos,_) -> tyPos
zonk bisubst ty@(TyVar NegRep tv ) = case M.lookup tv (unBisubstitution bisubst) of
    Nothing -> ty -- Recursive variable!
    Just (_,tyNeg) -> tyNeg
zonk bisubst (TyData rep tn xtors) = TyData rep tn (zonkXtorSig bisubst <$> xtors)
zonk bisubst (TyCodata rep tn xtors) = TyCodata rep tn (zonkXtorSig bisubst <$> xtors)
zonk _       (TyNominal rep tn) = TyNominal rep tn
zonk bisubst (TySet rep tys) = TySet rep (zonk bisubst <$> tys)
zonk bisubst (TyRec rep tv ty) = TyRec rep tv (zonk bisubst ty)

zonkPrdCnsType :: Bisubstitution -> PrdCnsType pol -> PrdCnsType pol
zonkPrdCnsType bisubst (PrdType ty) = PrdType (zonk bisubst ty)
zonkPrdCnsType bisubst (CnsType ty) = CnsType (zonk bisubst ty)

zonkLinearCtxt :: Bisubstitution -> LinearContext pol -> LinearContext pol
zonkLinearCtxt bisubst = fmap (zonkPrdCnsType bisubst)

zonkXtorSig :: Bisubstitution -> XtorSig pol -> XtorSig pol
zonkXtorSig bisubst (MkXtorSig name ctxt) =
    MkXtorSig name (zonkLinearCtxt bisubst ctxt)
    