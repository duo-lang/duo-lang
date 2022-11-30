module Translate.ResolveType where

import qualified Syntax.TST.Types as TST
import qualified Syntax.RST.Types as RST
import Syntax.CST.Kinds (MonoKind(..), EvaluationOrder (..))


class ResolveType a b | a -> b where
    resolveType :: a -> b

instance ResolveType (RST.XtorSig pol) (TST.XtorSig pol) where
    resolveType :: RST.XtorSig pol -> TST.XtorSig pol
    resolveType (RST.MkXtorSig xtor args) = TST.MkXtorSig xtor (resolveType <$> args)

instance ResolveType (RST.PrdCnsType pol) (TST.PrdCnsType pol) where
    resolveType (RST.PrdCnsType pc ty) = TST.PrdCnsType pc (resolveType ty)

instance ResolveType (RST.VariantType pol) (TST.VariantType pol) where
    resolveType :: RST.VariantType pol -> TST.VariantType pol
    resolveType (RST.CovariantType ty) = TST.CovariantType (resolveType ty)
    resolveType (RST.ContravariantType ty) = TST.ContravariantType (resolveType ty)

instance ResolveType (RST.Typ pol) (TST.Typ pol) where
    resolveType :: RST.Typ pol -> TST.Typ pol
    resolveType (RST.TySkolemVar loc pol var) = TST.TySkolemVar loc pol (CBox CBV) var
    resolveType (RST.TyUniVar loc pol var) = TST.TyUniVar loc pol (CBox CBV) var
    resolveType (RST.TyRecVar loc pol var) = TST.TyRecVar loc pol (CBox CBV) var
    resolveType (RST.TyData loc pol xtors) = TST.TyData loc pol (CBox CBV) (resolveType <$> xtors)
    resolveType (RST.TyCodata loc pol xtors) = TST.TyCodata loc pol (CBox CBV) (resolveType <$> xtors)
    resolveType (RST.TyDataRefined loc pol rn xtors) = TST.TyDataRefined loc pol (CBox CBV) rn (resolveType <$> xtors)
    resolveType (RST.TyCodataRefined loc pol rn xtors) = TST.TyCodataRefined loc pol (CBox CBV) rn (resolveType <$> xtors)
    resolveType (RST.TyNominal loc pol rn xtors) = TST.TyNominal loc pol (CBox CBV) rn (resolveType <$> xtors)
    resolveType (RST.TySyn loc pol rn ty) = TST.TySyn loc pol rn (resolveType ty)
    resolveType (RST.TyBot loc) = TST.TyBot loc (CBox CBV)
    resolveType (RST.TyTop loc) = TST.TyTop loc (CBox CBV)
    resolveType (RST.TyUnion loc ty1 ty2) = TST.TyUnion loc (CBox CBV) (resolveType ty1) (resolveType ty2)
    resolveType (RST.TyInter loc ty1 ty2) = TST.TyInter loc (CBox CBV) (resolveType ty1) (resolveType ty2)
    resolveType (RST.TyRec loc pol recTVar ty) = TST.TyRec loc pol recTVar (resolveType ty)
    resolveType (RST.TyI64 loc pol) = TST.TyI64 loc pol
    resolveType (RST.TyF64 loc pol) = TST.TyF64 loc pol
    resolveType (RST.TyChar loc pol) = TST.TyChar loc pol
    resolveType (RST.TyString loc pol) = TST.TyString loc pol
    resolveType (RST.TyFlipPol pol ty) = TST.TyFlipPol pol (resolveType ty)
    resolveType (RST.TyKindAnnot _k _ty) = error "no TST representation for kind annotations"