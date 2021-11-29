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
    