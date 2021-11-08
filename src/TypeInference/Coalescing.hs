module TypeInference.Coalescing where

import Control.Monad.State
import Control.Monad.Reader
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T

import Syntax.Types
import TypeInference.Constraints

---------------------------------------------------------------------------------
-- Bisubstitution
---------------------------------------------------------------------------------

type Bisubstitution = (Map TVar (Typ Pos, Typ Neg))

---------------------------------------------------------------------------------
-- Coalescing
---------------------------------------------------------------------------------

type CoalesceState  = (Int, Map (TVar, Polarity) TVar)
type CoalesceReader = SolverResult 

type CoalesceM  a = ReaderT CoalesceReader (State CoalesceState) a

runCoalesceM :: SolverResult ->  CoalesceM a -> a
runCoalesceM res m = evalState (runReaderT m res) (0,M.empty)

freshRecVar :: CoalesceM TVar
freshRecVar = do
    i <- gets fst
    modify (\(i,m) -> (i + 1, m))
    return (MkTVar (T.pack $ show i))

coalesce :: SolverResult -> Bisubstitution
coalesce result = M.fromList xs
    where
        res = M.keys result
        f tvar = (tvar, ( runCoalesceM result $ coalesceType $ TyVar PosRep tvar
                        , runCoalesceM result $ coalesceType $ TyVar NegRep tvar))
        xs = f <$> res

coalesceType :: Typ pol -> CoalesceM (Typ pol)
coalesceType (TyVar PosRep tv) = do
    mp <- gets snd
    case M.lookup (tv, Pos) mp of
        Nothing -> do
            variableState <- ask
            case M.lookup tv variableState of
                Nothing -> error "Not in variable state"
                Just VariableState { vst_lowerbounds } -> do
                    recVar <- freshRecVar
                    modify (\(i,m) -> (i,M.insert (tv, Pos) recVar m)) 
                    lbs' <- sequence $ coalesceType <$> vst_lowerbounds
                    return (TyRec PosRep recVar (TySet PosRep lbs'))
        (Just recvar) -> return (TyVar PosRep recvar)
coalesceType (TyVar NegRep tv) = do
    mp <- gets snd
    case M.lookup (tv, Neg) mp of
      Nothing -> do
          variableState <- ask
          case M.lookup tv variableState of
              Nothing -> error "Not in variable state"
              Just VariableState { vst_upperbounds } -> do
                  recVar <- freshRecVar
                  modify (\(i,m) -> (i,M.insert (tv, Neg) recVar m)) 
                  ubs' <- sequence $ coalesceType <$> vst_upperbounds
                  return (TyRec NegRep recVar (TySet NegRep ubs'))
      Just recvar -> return (TyVar NegRep recvar)
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
coalesceType (TyRec rep tv ty) = do
    ty' <- coalesceType ty
    return $ TyRec rep tv ty'

coalesceXtor :: XtorSig pol -> CoalesceM (XtorSig pol)
coalesceXtor (MkXtorSig name (MkTypArgs  prdArgs cnsArgs)) = do
    prdArgs' <- sequence $ coalesceType <$> prdArgs
    cnsArgs' <- sequence $ coalesceType <$> cnsArgs
    return $ MkXtorSig name (MkTypArgs prdArgs' cnsArgs')

---------------------------------------------------------------------------------
-- Zonking
---------------------------------------------------------------------------------

zonk :: Bisubstitution -> Typ pol -> Typ pol
zonk bisubst ty@(TyVar PosRep tv ) = case M.lookup tv bisubst of
    Nothing -> ty -- Recursive variable!
    Just (tyPos,_) -> tyPos
zonk bisubst ty@(TyVar NegRep tv ) = case M.lookup tv bisubst of
    Nothing -> ty -- Recursive variable!
    Just (_,tyNeg) -> tyNeg
zonk bisubst (TyData rep tn xtors) = TyData rep tn (zonkXtorSig bisubst <$> xtors)
zonk bisubst (TyCodata rep tn xtors) = TyCodata rep tn (zonkXtorSig bisubst <$> xtors)
zonk _       (TyNominal rep tn) = TyNominal rep tn
zonk bisubst (TySet rep tys) = TySet rep (zonk bisubst <$> tys)
zonk bisubst (TyRec rep tv ty) = TyRec rep tv (zonk bisubst ty)

zonkXtorSig :: Bisubstitution -> XtorSig pol -> XtorSig pol
zonkXtorSig bisubst (MkXtorSig name (MkTypArgs prdArgs cnsArgs)) =
    MkXtorSig name (MkTypArgs (zonk bisubst <$> prdArgs) (zonk bisubst <$> cnsArgs))
    