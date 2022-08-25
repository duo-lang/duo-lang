module TypeInference.GenerateConstraints.KindInference where

import Syntax.RST.Types qualified as RST
import Syntax.TST.Types qualified as TST
import Syntax.TST.Types (getKind)
import Syntax.CST.Kinds
import Syntax.CST.Names (SkolemTVar(unSkolemTVar), UniTVar (unUniTVar), RecTVar (unRecTVar))

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
checkKind (RST.TySkolemVar loc pol tv) = do
  let knd = KindVar (MkKVar (unSkolemTVar tv))
  TST.TySkolemVar loc pol (Just knd) tv 

checkKind (RST.TyUniVar loc pol tv) = do 
  let knd = KindVar (MkKVar (unUniTVar tv))
  TST.TyUniVar loc pol (Just knd) tv 

checkKind (RST.TyRecVar loc pol rv) = do
  let knd = KindVar (MkKVar (unRecTVar rv))
  TST.TyRecVar loc pol (Just knd) rv 

checkKind (RST.TyData loc pol xtors) = TST.TyData loc pol Nothing (map checkXtorSig xtors)                            -- TODO
checkKind (RST.TyCodata loc pol xtors) = TST.TyCodata loc pol Nothing (map checkXtorSig xtors)                        -- TODO
checkKind (RST.TyDataRefined loc pol tn xtors) = TST.TyDataRefined loc pol Nothing tn (map checkXtorSig xtors)        -- TODO
checkKind (RST.TyCodataRefined loc pol tn xtors) = TST.TyCodataRefined loc pol Nothing tn (map checkXtorSig xtors)    -- TODO
checkKind (RST.TyNominal loc pol tn vart) = TST.TyNominal loc pol Nothing tn (map checkVariantType vart)   -- TODO

checkKind (RST.TySyn loc pol tn ty) = TST.TySyn loc pol tn (checkKind ty) 

checkKind (RST.TyBot loc) = TST.TyBot loc (Just topbotVar)
checkKind (RST.TyTop loc) = TST.TyTop loc (Just topbotVar)
checkKind (RST.TyUnion loc ty1 ty2) = do 
  let ty1' = checkKind ty1
  let ty2' = checkKind ty2
  let knd = getKind ty1'
  if knd == getKind ty2' then
    TST.TyUnion loc knd (checkKind ty1) (checkKind ty2)
  else
    error ("Union of types " <> show ty1 <> " and " <> show ty2 <> " with different kinds")

checkKind (RST.TyInter loc ty1 ty2) = do
  let ty1' = checkKind ty1
  let ty2' = checkKind ty2
  let knd = getKind ty1'
  if knd == getKind ty2' then
    TST.TyInter loc knd (checkKind ty1) (checkKind ty2)
  else
    error ("Intersection of types " <> show ty1 <> " and " <> show ty2 <> " with different kinds")

checkKind (RST.TyRec loc pol rv ty) = TST.TyRec loc pol rv (checkKind ty)
checkKind (RST.TyI64 loc pol) = TST.TyI64 loc pol
checkKind (RST.TyF64 loc pol) = TST.TyF64 loc pol
checkKind (RST.TyChar loc pol) = TST.TyChar loc pol
checkKind (RST.TyString loc pol) = TST.TyString loc pol
checkKind (RST.TyFlipPol pol ty) = TST.TyFlipPol pol (checkKind ty)
