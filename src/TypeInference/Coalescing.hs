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

type CoalesceState  = Int 
type CoalesceReader = (SolverResult, Map (TVar, Polarity) TVar)

type CoalesceM  a = ReaderT CoalesceReader (State CoalesceState) a

runCoalesceM :: SolverResult ->  CoalesceM a -> a
runCoalesceM res m = evalState (runReaderT m (res,M.empty)) 0

freshRecVar :: CoalesceM TVar
freshRecVar = do
    i <- get
    modify (+1) 
    return (MkTVar (T.pack $ show i))

getVariableState :: TVar -> CoalesceM VariableState
getVariableState tv = do
    mp <- asks fst
    case M.lookup tv mp of
      Nothing -> error ("Not in variable states: " ++ show (tvar_name tv))
      Just vs -> return vs

coalesce :: SolverResult -> Bisubstitution
coalesce result = M.fromList xs
    where
        res = M.keys result
        f tvar = (tvar, ( runCoalesceM result $ coalesceType $ TyVar PosRep tvar
                        , runCoalesceM result $ coalesceType $ TyVar NegRep tvar))
        xs = f <$> res

coalesceType :: Typ pol -> CoalesceM (Typ pol)
coalesceType (TyVar PosRep tv) = do
    mp <- asks snd
    case M.lookup (tv, Pos) mp of
        Nothing -> do
            VariableState { vst_lowerbounds } <- getVariableState tv
            recVar <- freshRecVar
            let f (i,m) = (i,M.insert (tv, Pos) recVar m)
            lbs' <- local f $ sequence $ coalesceType <$> vst_lowerbounds
            return (TyRec PosRep recVar (TySet PosRep (TyVar PosRep recVar:lbs')))
        (Just recvar) -> return (TyVar PosRep recvar)
coalesceType (TyVar NegRep tv) = do
    mp <- asks snd
    case M.lookup (tv, Neg) mp of
      Nothing -> do
          VariableState {vst_upperbounds } <- getVariableState tv
          recVar <- freshRecVar
          let f (i,m) = (i,M.insert (tv, Neg) recVar m)
          ubs' <- local f $ sequence $ coalesceType <$> vst_upperbounds
          return (TyRec NegRep recVar (TySet NegRep (TyVar NegRep recVar:ubs')))
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
coalesceType (TyRec PosRep tv ty) = do
    let f (i,m) = (i, M.insert (tv, Pos) tv m)
    ty' <- local f $ coalesceType ty
    return $ TyRec PosRep tv ty'
coalesceType (TyRec NegRep tv ty) = do
    let f (i,m) = (i, M.insert (tv, Neg) tv m)
    ty' <- local f $ coalesceType ty
    return $ TyRec NegRep tv ty'

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
    