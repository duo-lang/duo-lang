module Resolution.Types (resolveTyp, resolveTypeScheme, resolveXTorSigs) where

import Control.Monad.Except (throwError)
import Data.Set qualified as S
import Data.List.NonEmpty (NonEmpty((:|)))

import Errors
import Resolution.Definition
import Resolution.SymbolTable
import Syntax.Common
import Syntax.Common.TypesPol ( freeTVars )
import Syntax.Common.TypesPol qualified as RST
import Syntax.Common.TypesUnpol
import Utils (Loc(..), defaultLoc)

import Syntax.Common.Names

---------------------------------------------------------------------------------
-- Lowering & Polarization (CST -> RST)
---------------------------------------------------------------------------------

resolveTypeScheme :: PolarityRep pol -> TypeScheme -> ResolverM (RST.TypeScheme pol)
resolveTypeScheme rep TypeScheme { ts_loc, ts_vars, ts_monotype } = do
    monotype <- resolveTyp rep ts_monotype
    if freeTVars monotype `S.isSubsetOf` S.fromList ts_vars
    then pure (RST.TypeScheme ts_loc ts_vars monotype)
        else throwError (LowerError ts_loc MissingVarsInTypeScheme :| [])

resolveTyp :: PolarityRep pol -> Typ -> ResolverM (RST.Typ pol)
resolveTyp rep (TyUniVar loc v) =
    pure $ RST.TyUniVar loc rep Nothing v
resolveTyp rep (TySkolemVar loc v) = 
    pure $ RST.TySkolemVar loc rep Nothing v
resolveTyp rep (TyRecVar loc v) = 
    pure $ RST.TySkolemVar loc rep Nothing (recTVarToSkolemTVar v)

-- Nominal Data
resolveTyp rep (TyXData loc Data sigs) = do
    sigs <- resolveXTorSigs rep sigs
    pure $ RST.TyData loc rep sigs
-- Refinement Data
resolveTyp rep (TyXRefined loc Data tn sigs) = do
    NominalResult tn' _ _ _ <- lookupTypeConstructor loc tn
    sigs <- resolveXTorSigs rep sigs
    pure $ RST.TyDataRefined loc rep tn' sigs
-- Nominal Codata
resolveTyp rep (TyXData loc Codata sigs) = do
    sigs <- resolveXTorSigs (flipPolarityRep rep) sigs
    pure $ RST.TyCodata loc rep sigs
-- Refinement Codata
resolveTyp rep (TyXRefined loc Codata tn sigs) = do
    NominalResult tn' _ _ _ <- lookupTypeConstructor loc tn
    sigs <- resolveXTorSigs (flipPolarityRep rep) sigs
    pure $ RST.TyCodataRefined loc rep tn' sigs
resolveTyp rep (TyNominal loc name args) = do
    res <- lookupTypeConstructor loc name
    case res of
        SynonymResult name' typ -> case args of
            [] -> do
                typ' <- resolveTyp rep typ
                pure $ RST.TySyn loc rep name' typ'
            _ -> throwOtherError loc ["Type synonyms cannot be applied to arguments (yet)."]
        NominalResult _ _ Refined _ -> do
            throwOtherError loc ["Refined type cannot be used as a nominal type constructor."]
        NominalResult name' _ NotRefined polykind -> do
            args' <- resolveTypeArgs loc rep name polykind args
            pure $ RST.TyNominal loc rep Nothing name' args'
resolveTyp rep (TyRec loc v typ) =
        RST.TyRec loc rep v <$> resolveTyp rep typ

-- Lattice types    
resolveTyp PosRep (TyTop loc) =
    throwError (LowerError loc TopInPosPolarity :| [])
resolveTyp NegRep (TyTop loc) =
    pure $ RST.TyTop loc Nothing
resolveTyp PosRep (TyBot loc) =
    pure $ RST.TyBot loc Nothing
resolveTyp NegRep (TyBot loc) =
    throwError (LowerError loc BotInNegPolarity :| [])
resolveTyp rep (TyBinOpChain fst rest) =
    resolveBinOpChain rep fst rest
resolveTyp rep (TyBinOp loc fst op snd) =
    resolveBinOp loc rep fst op snd
resolveTyp rep (TyParens _loc typ) =
    resolveTyp rep typ
resolveTyp rep (TyPrim loc pt) =
    pure $ RST.TyPrim loc rep pt



resolveTypeArgs :: forall pol. Loc -> PolarityRep pol -> TypeName -> PolyKind -> [Typ] -> ResolverM [RST.VariantType pol]
resolveTypeArgs loc rep tn MkPolyKind{ kindArgs } args = do
    if length args /= length kindArgs  then
        throwOtherError loc ["Type constructor " <> unTypeName tn <> " must be fully applied"]
    else do
        let
            f :: ((Variance, SkolemTVar, MonoKind), Typ) -> ResolverM (RST.VariantType pol)
            f ((Covariant,_,_),ty) = RST.CovariantType <$> resolveTyp rep ty
            f ((Contravariant,_,_),ty) = RST.ContravariantType <$> resolveTyp (flipPolarityRep rep) ty
        sequence (f <$> zip kindArgs args)


resolveXTorSigs :: PolarityRep pol -> [XtorSig] -> ResolverM [RST.XtorSig pol]
resolveXTorSigs rep sigs = sequence $ resolveXTorSig rep <$> sigs

resolveXTorSig :: PolarityRep pol -> XtorSig -> ResolverM (RST.XtorSig pol)
resolveXTorSig rep (MkXtorSig name ctx) = RST.MkXtorSig name <$> resolveLinearContext rep ctx

resolveLinearContext :: PolarityRep pol -> LinearContext -> ResolverM (RST.LinearContext pol)
resolveLinearContext rep ctx = sequence $ resolvePrdCnsTyp rep <$> ctx

resolvePrdCnsTyp :: PolarityRep pol -> PrdCnsTyp -> ResolverM (RST.PrdCnsType pol)
resolvePrdCnsTyp rep (PrdType typ) = RST.PrdCnsType PrdRep <$> resolveTyp rep typ
resolvePrdCnsTyp rep (CnsType typ) = RST.PrdCnsType CnsRep <$> resolveTyp (flipPolarityRep rep) typ

resolveBinOpChain :: PolarityRep pol -> Typ -> NonEmpty(Loc, BinOp, Typ) -> ResolverM (RST.Typ pol)
resolveBinOpChain rep fst rest = do
    op <- associateOps fst rest
    resolveTyp rep op

---------------------------------------------------------------------------------
-- Operator Desugaring
---------------------------------------------------------------------------------

desugaring :: Loc -> PolarityRep pol -> TyOpDesugaring -> Typ -> Typ -> ResolverM (RST.Typ pol)
desugaring loc PosRep UnionDesugaring tl tr = do
    tl <- resolveTyp PosRep tl
    tr <- resolveTyp PosRep tr
    pure $ RST.TyUnion loc Nothing tl tr
desugaring loc NegRep UnionDesugaring _ _ =
    throwError (LowerError loc UnionInNegPolarity :| [])
desugaring loc NegRep InterDesugaring tl tr = do
    tl <- resolveTyp NegRep tl
    tr <- resolveTyp NegRep tr
    pure $ RST.TyInter loc Nothing tl tr
desugaring loc PosRep InterDesugaring _ _ =
    throwError (LowerError loc IntersectionInPosPolarity :| [])
desugaring loc rep (NominalDesugaring tyname) tl tr = do
    resolveTyp rep (TyNominal loc tyname [tl, tr])

-- | Operator precedence parsing
-- Transforms "TyBinOpChain" into "TyBinOp"'s while nesting nodes
-- according to the defined operator associativity
--
-- Consider the following chain of types and operators:
-- @
-- τ0 \<1\> τ1 \<2\> τ2 ... \<n\> τn
-- @
-- where @\<1\> ... \<n\>@ are operators, τ0 ... τn are types.
--
-- Then, the following cases can occur:
--
--   * \<2\> has a higher priority or \<1\> is right associative:
--     parse @τ1 \<2\> ... \<n\> τn@ to @r@, then create the node @τ0 \<1\> r@
--
--   * \<1\> has a higher priority and \<1\> is left associative:
--     create the node @τ0 \<1\> τ1@ as @r@, then parse @r \<2\> ... \<n\>@
associateOps :: Typ -> NonEmpty (Loc, BinOp, Typ) -> ResolverM Typ
associateOps lhs ((loc, s, rhs) :| []) = pure $ TyBinOp loc lhs s rhs
associateOps lhs ((loc1, s1, rhs1) :| next@(loc2, s2, _rhs2) : rest) = do
    (_,op1) <- lookupTyOp loc1 s1
    (_,op2) <- lookupTyOp loc2 s2
    if prec op2 > prec op1 || (assoc op1 == RightAssoc)
    then do
        rhs <- associateOps rhs1 (next :| rest)
        pure $ TyBinOp loc1 lhs s1 rhs
    else if assoc op1 == LeftAssoc
    then do
        associateOps (TyBinOp loc1 lhs s1 rhs1) (next :| rest)
    else
        throwOtherError defaultLoc ["Unhandled case reached. This is a bug the operator precedence parser"]

resolveBinOp :: Loc -> PolarityRep pol -> Typ -> BinOp -> Typ -> ResolverM (RST.Typ pol)
resolveBinOp loc rep lhs s rhs = do
    (_,op) <- lookupTyOp loc s
    desugaring loc rep (desugar op) lhs rhs
