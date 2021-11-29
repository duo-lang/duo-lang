module Syntax.Zonking where

import Data.Map (Map)
import Data.Map qualified as M

import Syntax.Types

--------------------------------------------------------------------------------
-- Bisubstitution
---------------------------------------------------------------------------------

newtype Bisubstitution = MkBisubstitution { unBisubstitution :: Map TVar (Typ Pos, Typ Neg) }

---------------------------------------------------------------------------------
-- Zonking
---------------------------------------------------------------------------------

zonkType :: Bisubstitution -> Typ pol -> Typ pol
zonkType bisubst ty@(TyVar PosRep tv ) = case M.lookup tv (unBisubstitution bisubst) of
    Nothing -> ty -- Recursive variable!
    Just (tyPos,_) -> tyPos
zonkType bisubst ty@(TyVar NegRep tv ) = case M.lookup tv (unBisubstitution bisubst) of
    Nothing -> ty -- Recursive variable!
    Just (_,tyNeg) -> tyNeg
zonkType bisubst (TyData rep tn xtors) = TyData rep tn (zonkXtorSig bisubst <$> xtors)
zonkType bisubst (TyCodata rep tn xtors) = TyCodata rep tn (zonkXtorSig bisubst <$> xtors)
zonkType _       (TyNominal rep tn) = TyNominal rep tn
zonkType bisubst (TySet rep tys) = TySet rep (zonkType bisubst <$> tys)
zonkType bisubst (TyRec rep tv ty) = TyRec rep tv (zonkType bisubst ty)

zonkPrdCnsType :: Bisubstitution -> PrdCnsType pol -> PrdCnsType pol
zonkPrdCnsType bisubst (PrdType ty) = PrdType (zonkType bisubst ty)
zonkPrdCnsType bisubst (CnsType ty) = CnsType (zonkType bisubst ty)

zonkLinearCtxt :: Bisubstitution -> LinearContext pol -> LinearContext pol
zonkLinearCtxt bisubst = fmap (zonkPrdCnsType bisubst)

zonkXtorSig :: Bisubstitution -> XtorSig pol -> XtorSig pol
zonkXtorSig bisubst (MkXtorSig name ctxt) =
    MkXtorSig name (zonkLinearCtxt bisubst ctxt)
    