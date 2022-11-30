module Translate.ResolveType where

import qualified Syntax.TST.Types as TST
import qualified Syntax.RST.Types as RST
import Syntax.CST.Kinds (MonoKind(..))


class ResolveType a b | a -> b where
    resolveType :: MonoKind -> a -> b

instance ResolveType (RST.XtorSig pol) (TST.XtorSig pol) where
    resolveType :: MonoKind -> RST.XtorSig pol -> TST.XtorSig pol
    resolveType k (RST.MkXtorSig xtor args) = TST.MkXtorSig xtor (resolveType k <$> args)

instance ResolveType (RST.PrdCnsType pol) (TST.PrdCnsType pol) where
    resolveType k (RST.PrdCnsType pc ty) = TST.PrdCnsType pc (resolveType k ty)

instance ResolveType (RST.VariantType pol) (TST.VariantType pol) where
    resolveType :: MonoKind -> RST.VariantType pol -> TST.VariantType pol
    resolveType k (RST.CovariantType ty) = TST.CovariantType (resolveType k ty)
    resolveType k (RST.ContravariantType ty) = TST.ContravariantType (resolveType k ty)

instance ResolveType (RST.Typ pol) (TST.Typ pol) where
    resolveType :: MonoKind -> RST.Typ pol -> TST.Typ pol
    resolveType k (RST.TySkolemVar loc pol var) = TST.TySkolemVar loc pol k var
    resolveType k (RST.TyUniVar loc pol var) = TST.TyUniVar loc pol k var
    resolveType k (RST.TyRecVar loc pol var) = TST.TyRecVar loc pol k var
    resolveType k (RST.TyData loc pol xtors) = TST.TyData loc pol k (resolveType k <$> xtors)
    resolveType k (RST.TyCodata loc pol xtors) = TST.TyCodata loc pol k (resolveType k <$> xtors)
    resolveType k (RST.TyDataRefined loc pol rn xtors) = TST.TyDataRefined loc pol k rn (resolveType k <$> xtors)
    resolveType k (RST.TyCodataRefined loc pol rn xtors) = TST.TyCodataRefined loc pol k rn (resolveType k <$> xtors)
    resolveType k (RST.TyNominal loc pol rn xtors) = TST.TyNominal loc pol k rn (resolveType k <$> xtors)
    resolveType k (RST.TySyn loc pol rn ty) = TST.TySyn loc pol rn (resolveType k ty)
    resolveType k (RST.TyBot loc) = TST.TyBot loc k
    resolveType k (RST.TyTop loc) = TST.TyTop loc k
    resolveType k (RST.TyUnion loc ty1 ty2) = TST.TyUnion loc k (resolveType k ty1) (resolveType k ty2)
    resolveType k (RST.TyInter loc ty1 ty2) = TST.TyInter loc k (resolveType k ty1) (resolveType k ty2)
    resolveType k (RST.TyRec loc pol recTVar ty) = TST.TyRec loc pol recTVar (resolveType k ty)
    resolveType _k (RST.TyI64 loc pol) = TST.TyI64 loc pol
    resolveType _k (RST.TyF64 loc pol) = TST.TyF64 loc pol
    resolveType _k (RST.TyChar loc pol) = TST.TyChar loc pol
    resolveType _k (RST.TyString loc pol) = TST.TyString loc pol
    resolveType k (RST.TyFlipPol pol ty) = TST.TyFlipPol pol (resolveType k ty)
    resolveType _k (RST.TyKindAnnot _k' _ty) = error "no TST representation for kind annotations"