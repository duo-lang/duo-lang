module Syntax.Zonking where

import Data.Map (Map)
import Data.Map qualified as M

import Syntax.CommonTerm
import Syntax.AST.Terms
import Syntax.AST.Types
import Syntax.Kinds

--------------------------------------------------------------------------------
-- Bisubstitution
---------------------------------------------------------------------------------

data Bisubstitution = MkBisubstitution { uvarSubst :: Map TVar (Typ Pos, Typ Neg)
                                       , kvarSubst :: Map KVar Kind
                                       }

---------------------------------------------------------------------------------
-- Zonking of Types
---------------------------------------------------------------------------------

zonkType :: Bisubstitution -> Typ pol -> Typ pol
zonkType bisubst ty@(TyVar PosRep _ tv) = case M.lookup tv (uvarSubst bisubst) of
    Nothing -> ty -- Recursive variable!
    Just (tyPos,_) -> tyPos
zonkType bisubst ty@(TyVar NegRep _ tv) = case M.lookup tv (uvarSubst bisubst) of
    Nothing -> ty -- Recursive variable!
    Just (_,tyNeg) -> tyNeg
zonkType bisubst (TyData rep tn xtors) = TyData rep tn (zonkXtorSig bisubst <$> xtors)
zonkType bisubst (TyCodata rep tn xtors) = TyCodata rep tn (zonkXtorSig bisubst <$> xtors)
zonkType bisubst (TyNominal rep kind tn) = TyNominal rep (zonkKind bisubst <$> kind) tn
zonkType bisubst (TySet rep kind tys) = TySet rep (zonkKind bisubst <$> kind) (zonkType bisubst <$> tys)
zonkType bisubst (TyRec rep tv ty) = TyRec rep tv (zonkType bisubst ty)

zonkKind :: Bisubstitution -> Kind -> Kind
zonkKind _ (MonoKind cc) = MonoKind cc
zonkKind bisubst kind@(KindVar kv) = case M.lookup kv (kvarSubst bisubst) of
    Nothing -> kind
    Just kind' -> kind'

zonkPrdCnsType :: Bisubstitution -> PrdCnsType pol -> PrdCnsType pol
zonkPrdCnsType bisubst (PrdCnsType rep ty) = PrdCnsType rep (zonkType bisubst ty)

zonkLinearCtxt :: Bisubstitution -> LinearContext pol -> LinearContext pol
zonkLinearCtxt bisubst = fmap (zonkPrdCnsType bisubst)

zonkXtorSig :: Bisubstitution -> XtorSig pol -> XtorSig pol
zonkXtorSig bisubst (MkXtorSig name ctxt) =
    MkXtorSig name (zonkLinearCtxt bisubst ctxt)

---------------------------------------------------------------------------------
-- Zonking of Terms
---------------------------------------------------------------------------------

zonkTerm :: Bisubstitution -> Term pc Inferred -> Term pc Inferred
zonkTerm bisubst (BoundVar (loc,ty) rep idx) =
    BoundVar (loc, zonkType bisubst ty) rep idx
zonkTerm bisubst (FreeVar  (loc,ty) rep nm)  =
    FreeVar  (loc, zonkType bisubst ty) rep nm
zonkTerm bisubst (Xtor (loc,ty) rep xn subst) =
    Xtor (loc, zonkType bisubst ty) rep xn (zonkPCTerm bisubst <$> subst)
zonkTerm bisubst (XMatch (loc,ty) rep ns cases) =
    XMatch (loc, zonkType bisubst ty) rep ns (zonkCmdCase bisubst <$> cases)
zonkTerm bisubst (MuAbs (loc,ty) rep fv cmd) =
    MuAbs (loc, zonkType bisubst ty) rep fv (zonkCommand bisubst cmd)
zonkTerm bisubst (Dtor (loc,ty) xt prd (subst1,pcrep,subst2)) =
    Dtor (loc, zonkType bisubst ty) xt (zonkTerm bisubst prd) (zonkPCTerm bisubst <$> subst1,pcrep,zonkPCTerm bisubst <$> subst2)
zonkTerm bisubst (Case (loc,ty) ns prd cases) =
    Case (loc, zonkType bisubst ty) ns (zonkTerm bisubst prd) (zonkTermCase bisubst <$> cases)
zonkTerm bisubst (Cocase (loc,ty) ns cases) =
    Cocase (loc, zonkType bisubst ty) ns (zonkTermCaseI bisubst <$> cases)

zonkPCTerm :: Bisubstitution -> PrdCnsTerm Inferred -> PrdCnsTerm Inferred
zonkPCTerm bisubst (PrdTerm tm) = PrdTerm (zonkTerm bisubst tm)
zonkPCTerm bisubst (CnsTerm tm) = CnsTerm (zonkTerm bisubst tm)

zonkCmdCase :: Bisubstitution -> CmdCase Inferred -> CmdCase Inferred
zonkCmdCase bisubst (MkCmdCase loc nm args cmd) = MkCmdCase loc nm args (zonkCommand bisubst cmd)

zonkTermCase :: Bisubstitution -> TermCase Inferred -> TermCase  Inferred
zonkTermCase bisubst (MkTermCase loc nm args tm) = MkTermCase loc nm args (zonkTerm bisubst tm)

zonkTermCaseI :: Bisubstitution -> TermCaseI Inferred -> TermCaseI  Inferred
zonkTermCaseI bisubst (MkTermCaseI loc nm args tm) = MkTermCaseI loc nm args (zonkTerm bisubst tm)

zonkCommand :: Bisubstitution -> Command Inferred -> Command Inferred
zonkCommand bisubst (Apply ext kind prd cns) = Apply ext (zonkKind bisubst <$> kind) (zonkTerm bisubst prd) (zonkTerm bisubst cns)
zonkCommand bisubst (Print ext prd cmd) = Print ext (zonkTerm bisubst prd) (zonkCommand bisubst cmd)
zonkCommand bisubst (Read ext cns) = Read ext (zonkTerm bisubst cns)
zonkCommand _       (Call ext fv) = Call ext fv
zonkCommand _       (Done ext) = Done ext
