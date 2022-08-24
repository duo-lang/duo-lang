module TypeInference.GenerateConstraints.KindInference where

import Syntax.RST.Types qualified as RST
import Syntax.TST.Types qualified as TST
import Syntax.CST.Kinds
---------------------------------------------------------------------------------------------
-- Kinds
---------------------------------------------------------------------------------------------

checkTypeScheme :: RST.TypeScheme pol -> TST.TypeScheme pol
checkTypeScheme RST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = ty} = TST.TypeScheme {ts_loc = loc, ts_vars = tvs, ts_monotype = checkKind ty}

checkVariantType :: RST.VariantType pol -> TST.VariantType pol 
checkVariantType (RST.CovariantType ty) = TST.CovariantType (checkKind ty)
checkVariantType (RST.ContravariantType ty) = TST.ContravariantType (checkKind ty)

checkPrdCnsType :: RST.PrdCnsType pol -> TST.PrdCnsType pol
checkPrdCnsType (RST.PrdCnsType rep ty) = TST.PrdCnsType rep (checkKind ty)

checkLinearContext :: RST.LinearContext pol -> TST.LinearContext pol
checkLinearContext = map checkPrdCnsType

checkXtorSig :: RST.XtorSig pol -> TST.XtorSig pol
checkXtorSig RST.MkXtorSig { sig_name = nm, sig_args = ctxt } = TST.MkXtorSig {sig_name = nm, sig_args = checkLinearContext ctxt }

checkKind :: RST.Typ pol -> TST.Typ pol 
checkKind (RST.TySkolemVar loc pol tv) = TST.TySkolemVar loc pol (CBox CBV) tv
checkKind (RST.TyUniVar loc pol tv) = TST.TyUniVar loc pol (CBox CBV) tv
checkKind (RST.TyRecVar loc pol rv) = TST.TyRecVar loc pol (CBox CBV) rv
checkKind (RST.TyData loc pol xtors) = TST.TyData loc pol (map checkXtorSig xtors)
checkKind (RST.TyCodata loc pol xtors) = TST.TyCodata loc pol (map checkXtorSig xtors)
checkKind (RST.TyDataRefined loc pol tn xtors) = TST.TyDataRefined loc pol tn (map checkXtorSig xtors)
checkKind (RST.TyCodataRefined loc pol tn xtors) = TST.TyCodataRefined loc pol tn (map checkXtorSig xtors)
checkKind (RST.TyNominal loc pol tn vart) = TST.TyNominal loc pol (CBox CBV) tn (map checkVariantType vart)
checkKind (RST.TySyn loc pol tn ty) = TST.TySyn loc pol tn (checkKind ty)
checkKind (RST.TyBot loc) = TST.TyBot loc
checkKind (RST.TyTop loc) = TST.TyTop loc
checkKind (RST.TyUnion loc ty1 ty2) = TST.TyUnion loc (CBox CBV) (checkKind ty1) (checkKind ty2)
checkKind (RST.TyInter loc ty1 ty2) = TST.TyInter loc (CBox CBV) (checkKind ty1) (checkKind ty2)
checkKind (RST.TyRec loc pol rv ty) = TST.TyRec loc pol rv (checkKind ty)
checkKind (RST.TyI64 loc pol) = TST.TyI64 loc pol
checkKind (RST.TyF64 loc pol) = TST.TyF64 loc pol
checkKind (RST.TyChar loc pol) = TST.TyChar loc pol
checkKind (RST.TyString loc pol) = TST.TyString loc pol
checkKind (RST.TyFlipPol pol ty) = TST.TyFlipPol pol (checkKind ty)
