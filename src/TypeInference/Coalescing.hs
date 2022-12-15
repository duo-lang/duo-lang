module TypeInference.Coalescing ( coalesce ) where

import Control.Monad.State
import Control.Monad.Reader
import Data.Maybe (fromMaybe)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text qualified as T

import Syntax.TST.Types
import Syntax.RST.Types (PolarityRep(..),Polarity(..))
import Syntax.CST.Names
import TypeInference.Constraints
import Loc ( defaultLoc )

---------------------------------------------------------------------------------
-- Coalescing
---------------------------------------------------------------------------------

data CoalesceState  = CoalesceState 
  { s_var_counter :: Int
  , s_recursive :: Map (UniTVar, Polarity) RecTVar
  , s_uni_to_skolem :: Map UniTVar SkolemTVar
  }
data CoalesceReader = CoalesceReader
  { r_result :: SolverResult
  , r_inProcess :: Set (UniTVar, Polarity)
  }

type CoalesceM  a = ReaderT CoalesceReader (State CoalesceState) a

runCoalesceM :: SolverResult ->  CoalesceM a -> a
runCoalesceM res m = evalState (runReaderT m initialReader) initialState
  where
    initialState  = CoalesceState 0 M.empty M.empty
    initialReader = CoalesceReader res S.empty

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

getSkolemVar :: UniTVar -> CoalesceM SkolemTVar
getSkolemVar uv = do
  uts <- gets s_uni_to_skolem
  case M.lookup uv uts of
    Nothing -> do
      sv <- freshSkolemVar
      modify $ \s -> s { s_uni_to_skolem =  M.insert uv sv uts }
      return sv
    Just sv -> return sv

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
coalesce result@MkSolverResult { tvarSolution, kvarSolution } = MkBisubstitution (M.fromList xs,kvarSolution)
    where
        res = M.keys tvarSolution
        kinds = map (\x -> vst_kind (fromMaybe  (error "UniVar not found in SolverResult (should never happen)") (M.lookup x tvarSolution))) res
        f (tvar,mk) = do 
          x <- coalesceType $ TyUniVar defaultLoc PosRep mk tvar
          y <- coalesceType $ TyUniVar defaultLoc NegRep mk tvar
          return (x, y)
        xs = zip res $ runCoalesceM result $ mapM f (zip res kinds)

coalesceType :: Typ pol -> CoalesceM (Typ pol)
coalesceType (TySkolemVar loc rep mk tv) =  do
  return (TySkolemVar loc rep mk tv)
coalesceType (TyRecVar loc rep mk tv) = do 
  return (TyRecVar loc rep mk tv)
coalesceType (TyUniVar _ PosRep mk tv) = do
    isInProcess <- inProcess (tv, Pos)
    if isInProcess
        then do
            recVar <- getOrElseUpdateRecVar (tv, Pos)
            return (TyRecVar defaultLoc PosRep mk recVar)
        else do
            VariableState { vst_lowerbounds } <- getVariableState tv
            let f r = r { r_inProcess =  S.insert (tv, Pos) (r_inProcess r) }
            lbs' <- local f $ sequence $ coalesceType <$> vst_lowerbounds
            recVarMap <- gets s_recursive
            case M.lookup (tv, Pos) recVarMap of
                Nothing     -> do
                    newName <- getSkolemVar tv
                    return $                                            mkUnion defaultLoc mk (TySkolemVar defaultLoc PosRep mk newName : lbs')
                Just recVar -> return $ TyRec defaultLoc PosRep recVar (mkUnion defaultLoc mk (TyRecVar defaultLoc PosRep mk recVar  : lbs'))
coalesceType (TyUniVar _ NegRep mk tv) = do
    isInProcess <- inProcess (tv, Neg)
    if isInProcess
        then do
            recVar <- getOrElseUpdateRecVar (tv, Neg)
            return (TyRecVar defaultLoc NegRep mk recVar)
        else do
            VariableState { vst_upperbounds } <- getVariableState tv
            let f r = r { r_inProcess =  S.insert (tv, Neg) (r_inProcess r) }
            ubs' <- local f $ sequence $ coalesceType <$> vst_upperbounds
            recVarMap <- gets s_recursive
            case M.lookup (tv, Neg) recVarMap of
                Nothing     -> do
                    newName <- getSkolemVar tv
                    return $                                            mkInter defaultLoc mk (TySkolemVar defaultLoc NegRep mk newName : ubs')
                Just recVar -> return $ TyRec defaultLoc NegRep recVar (mkInter defaultLoc mk (TyRecVar defaultLoc NegRep mk recVar  : ubs'))
coalesceType (TyData loc rep mk xtors) = do
    xtors' <- sequence $ coalesceXtor <$> xtors
    return (TyData loc rep mk xtors')
coalesceType (TyCodata loc rep mk xtors) = do
    xtors' <- sequence $ coalesceXtor <$> xtors
    return (TyCodata loc rep mk xtors')
coalesceType (TyDataRefined loc rep mk tn xtors) = do
    xtors' <- sequence $ coalesceXtor <$> xtors
    return (TyDataRefined loc rep mk tn xtors')
coalesceType (TyCodataRefined loc rep mk tn xtors) = do
    xtors' <- sequence $ coalesceXtor <$> xtors
    return (TyCodataRefined loc rep mk tn xtors')
coalesceType (TyNominal loc rep mk tn) = do
    return $ TyNominal loc rep mk tn 
coalesceType (TyApp loc rep ty args) = do 
    args' <- sequence $ coalesceVariantType <$> args
    ty' <- coalesceType ty
    return $ TyApp loc rep ty' args'
coalesceType (TySyn _loc _rep _nm ty) = coalesceType ty
coalesceType (TyTop loc mk) = do 
    pure (TyTop loc mk)
coalesceType (TyBot loc mk) = do
    pure (TyBot loc mk)
coalesceType (TyUnion loc mk ty1 ty2) = do
  ty1' <- coalesceType ty1
  ty2' <- coalesceType ty2
  pure (TyUnion loc mk ty1' ty2')
coalesceType (TyInter loc mk ty1 ty2) = do
  ty1' <- coalesceType ty1
  ty2' <- coalesceType ty2
  pure (TyInter loc mk ty1' ty2')
coalesceType (TyRec loc PosRep tv ty) = do
    return $ TyRec loc PosRep tv ty
coalesceType (TyRec loc NegRep tv ty) = do
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

