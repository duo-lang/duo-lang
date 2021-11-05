module TypeInference.Coalescing where

import Data.Map (Map)
import Data.Map qualified as M

import Syntax.Types
import TypeInference.Constraints

type Bisubstitution = (Map TVar (Typ Pos, Typ Neg))

coalesce :: SolverResult -> Bisubstitution
coalesce result =
    let
        res = M.toList result
    in
    undefined

coalesceHelp :: [(TVar, VariableState)] -> TVar -> (Typ Pos, Typ Neg)
coalesceHelp res tv = undefined

coalesceType :: Monad m => Typ pol -> m (Typ pol)
coalesceType (TyVar PosRep _) = undefined
coalesceType (TyVar NegRep _) = undefined
coalesceType (TyData _ _ _) = undefined 
coalesceType (TyCodata _ _ _) = undefined
coalesceType (TyNominal rep tn) =
    return $ TyNominal rep tn
coalesceType (TySet rep tys) = do
    tys' <- sequence $ coalesceType <$> tys
    return (TySet rep tys')
coalesceType (TyRec rep tv ty) = do
    ty' <- coalesceType ty
    return $ TyRec rep tv ty'

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
    