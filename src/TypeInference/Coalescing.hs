module TypeInference.Coalescing ( coalesce ) where

import Control.Monad.State
import Control.Monad.Reader
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text qualified as T

import Syntax.TST.Types
import Syntax.Common.Names
import Syntax.Common.Polarity
import TypeInference.Constraints
import Utils

---------------------------------------------------------------------------------
-- Coalescing
---------------------------------------------------------------------------------

data CoalesceState  = CoalesceState  { s_var_counter :: Int, s_recursive :: Map (UniTVar, Polarity) RecTVar }
data CoalesceReader = CoalesceReader { r_result :: SolverResult, r_inProcess :: Set (UniTVar, Polarity) }

type CoalesceM  a = ReaderT CoalesceReader (State CoalesceState) a

runCoalesceM :: SolverResult ->  CoalesceM a -> a
runCoalesceM res m = evalState (runReaderT m (CoalesceReader res S.empty)) (CoalesceState 0 M.empty)

freshRecVar :: CoalesceM RecTVar
freshRecVar = do
    i <- gets s_var_counter
    modify (\s -> s { s_var_counter = i+1 } )
    return (MkRecTVar (T.pack $ "rr" ++ show i)) -- Use "rr" so that they don't clash.

freshSkolemVar :: CoalesceM SkolemTVar
freshSkolemVar = do
    i <- gets s_var_counter
    modify (\s -> s { s_var_counter = i+1 } )
    return (MkSkolemTVar (T.pack $ "s" ++ show i)) -- Use "s" so that they don't clash.

inProcess :: (UniTVar, Polarity) -> CoalesceM Bool
inProcess ptv = do
    inp <- asks r_inProcess
    return $ ptv `S.member` inp

getVariableState :: UniTVar -> CoalesceM VariableState
getVariableState tv = do
    mp <- asks (tvarSolution . r_result)
    case M.lookup tv mp of
      Nothing -> error ("Not in variable states: " ++ show (unUniTVar tv))
      Just vs -> return vs

getOrElseUpdateRecVar :: (UniTVar, Polarity) -> CoalesceM RecTVar
getOrElseUpdateRecVar ptv = do
    mp <- gets s_recursive
    case M.lookup ptv mp of
      Nothing -> do
          recVar <- freshRecVar
          modify (\s -> s { s_recursive = M.insert ptv recVar (s_recursive s) })
          return recVar
      Just tv -> return tv


coalesce :: SolverResult -> Bisubstitution UniVT
coalesce result@MkSolverResult { tvarSolution } = MkBisubstitution $ M.fromList xs
    where
        res = M.keys tvarSolution
        f tvar = do x <- coalesceType $ TyUniVar defaultLoc PosRep Nothing tvar
                    y <- coalesceType $ TyUniVar defaultLoc NegRep Nothing tvar
                    return (x, y)

        xs = zip res $ runCoalesceM result $ mapM f res

coalesceType :: Typ pol -> CoalesceM (Typ pol)
coalesceType (TySkolemVar loc rep mono tv) =  return (TySkolemVar loc rep mono tv)
coalesceType (TyRecVar loc rep mono tv) = return (TyRecVar loc rep mono tv)
coalesceType (TyUniVar _ PosRep _ tv) = do
    isInProcess <- inProcess (tv, Pos)
    if isInProcess
        then do
            recVar <- getOrElseUpdateRecVar (tv, Pos)
            return (TyRecVar defaultLoc PosRep Nothing recVar)
        else do
            VariableState { vst_lowerbounds } <- getVariableState tv
            let f r = r { r_inProcess =  S.insert (tv, Pos) (r_inProcess r) }
            lbs' <- local f $ sequence $ coalesceType <$> vst_lowerbounds
            recVarMap <- gets s_recursive
            case M.lookup (tv, Pos) recVarMap of
                Nothing     -> do
                    newName <- freshSkolemVar
                    return $                                            mkUnion defaultLoc Nothing (TySkolemVar defaultLoc PosRep Nothing newName : lbs')
                Just recVar -> return $ TyRec defaultLoc PosRep recVar (mkUnion defaultLoc Nothing (TyRecVar defaultLoc PosRep Nothing recVar  : lbs'))
coalesceType (TyUniVar _ NegRep _ tv) = do
    isInProcess <- inProcess (tv, Neg)
    if isInProcess
        then do
            recVar <- getOrElseUpdateRecVar (tv, Neg)
            return (TyRecVar defaultLoc NegRep Nothing recVar)
        else do
            VariableState { vst_upperbounds } <- getVariableState tv
            let f r = r { r_inProcess =  S.insert (tv, Neg) (r_inProcess r) }
            ubs' <- local f $ sequence $ coalesceType <$> vst_upperbounds
            recVarMap <- gets s_recursive
            case M.lookup (tv, Neg) recVarMap of
                Nothing     -> do
                    newName <- freshSkolemVar
                    return $                                            mkInter defaultLoc Nothing (TySkolemVar defaultLoc NegRep Nothing newName : ubs')
                Just recVar -> return $ TyRec defaultLoc NegRep recVar (mkInter defaultLoc Nothing (TyRecVar defaultLoc NegRep Nothing recVar  : ubs'))
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
    -- modify (second (M.insert (tv, Pos) tv))
    -- let f = second (S.insert (tv, Pos))
    -- ty' <- local f $ coalesceType ty
    return $ TyRec loc PosRep tv ty
coalesceType (TyRec loc NegRep tv ty) = do
    -- modify (second (M.insert (tv, Neg) tv))
    -- let f = second (S.insert (tv, Neg))
    -- ty' <- local f $ coalesceType ty
    return $ TyRec loc NegRep tv ty
coalesceType t@TyI64 {} = return t
coalesceType t@TyF64 {} = return t
coalesceType t@TyChar {} = return t
coalesceType t@TyString {} = return t
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

