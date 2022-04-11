module Renamer.Types (lowerTyp, lowerTypeScheme, lowerXTorSig) where

import Control.Monad.Except (throwError)
import Data.Set qualified as S
import Data.List.NonEmpty (NonEmpty((:|)))

import Errors
import Pretty.Pretty
import Renamer.Definition
import Renamer.SymbolTable
import Syntax.Common
import qualified Syntax.RST.Types as RST
import Syntax.RST.Types ( freeTVars )
import Syntax.CST.Types
import Data.List
import Utils (Loc(..))

---------------------------------------------------------------------------------
-- Lowering & Polarization (CST -> RST)
---------------------------------------------------------------------------------

lowerTypeScheme :: PolarityRep pol -> TypeScheme -> RenamerM (RST.TypeScheme pol)
lowerTypeScheme rep (TypeScheme { ts_loc, ts_vars, ts_monotype }) = do
    monotype <- lowerTyp rep ts_monotype
    if (freeTVars monotype) `S.isSubsetOf` (S.fromList ts_vars)
        then pure (RST.TypeScheme ts_loc ts_vars monotype)
        else throwError (LowerError (Just ts_loc) MissingVarsInTypeScheme)

lowerTyp :: PolarityRep pol -> Typ -> RenamerM (RST.Typ pol)
lowerTyp rep (TyVar loc v) =
    pure $ RST.TyVar loc rep Nothing v
lowerTyp rep (TyXData loc Data name sigs) = do
    sigs <- lowerXTorSigs rep sigs
    pure $ RST.TyData loc rep name sigs
lowerTyp rep (TyXData loc Codata name sigs) = do
    sigs <- lowerXTorSigs (flipPolarityRep rep) sigs
    pure $ RST.TyCodata loc rep name sigs
lowerTyp rep (TyNominal loc name args) = do
    res <- lookupTypeConstructor loc name
    case res of
        SynonymResult typ -> case args of
            [] -> lowerTyp rep typ
            _ -> throwError (OtherError (Just loc) "Type synonyms cannot be applied to arguments (yet).")
        NominalResult Refined _ -> do
            throwError (OtherError (Just loc) "Refined type cannot be used as a nominal type constructor.")
        NominalResult NotRefined polykind -> do
            args' <- lowerTypeArgs loc rep name polykind args
            pure $ RST.TyNominal loc rep Nothing name args'
lowerTyp rep (TyRec loc v typ) =
    RST.TyRec loc rep v <$> lowerTyp rep typ
lowerTyp PosRep (TyTop loc) = throwError (LowerError (Just loc) TopInPosPolarity)
lowerTyp NegRep (TyTop loc) =
    pure $ RST.TySet loc NegRep Nothing []
lowerTyp PosRep (TyBot loc) =
    pure $ RST.TySet loc PosRep Nothing []
lowerTyp NegRep (TyBot loc) =
    throwError (LowerError (Just loc) BotInNegPolarity)
lowerTyp rep (TyBinOpChain fst rest) =
    lowerBinOpChain rep fst rest
lowerTyp rep (TyBinOp loc fst op snd) =
    lowerBinOp loc rep fst op snd
lowerTyp rep (TyParens _loc typ) =
    lowerTyp rep typ
lowerTyp rep (TyPrim loc pt) =
    pure $ RST.TyPrim loc rep pt



lowerTypeArgs :: forall pol. Loc -> PolarityRep pol -> TypeName -> PolyKind -> [Typ] -> RenamerM [RST.VariantType pol]
lowerTypeArgs loc rep tn (MkPolyKind { kindArgs }) args = do
    if (length args) /= length kindArgs  then
        throwError (OtherError (Just loc) ("Type constructor " <> unTypeName tn <> " must be fully applied"))
    else do
        let
            f :: ((Variance, TVar, MonoKind), Typ) -> RenamerM (RST.VariantType pol)
            f ((Covariant,_,_),ty) = RST.CovariantType <$> lowerTyp rep ty
            f ((Contravariant,_,_),ty) = RST.ContravariantType <$> lowerTyp (flipPolarityRep rep) ty
        sequence (f <$> zip kindArgs args)
        

lowerXTorSigs :: PolarityRep pol -> [XtorSig] -> RenamerM [RST.XtorSig pol]
lowerXTorSigs rep sigs = sequence $ lowerXTorSig rep <$> sigs

lowerXTorSig :: PolarityRep pol -> XtorSig -> RenamerM (RST.XtorSig pol)
lowerXTorSig rep (MkXtorSig name ctx) = RST.MkXtorSig name <$> lowerLinearContext rep ctx

lowerLinearContext :: PolarityRep pol -> LinearContext -> RenamerM (RST.LinearContext pol)
lowerLinearContext rep ctx = sequence $ lowerPrdCnsTyp rep <$> ctx

lowerPrdCnsTyp :: PolarityRep pol -> PrdCnsTyp -> RenamerM (RST.PrdCnsType pol)
lowerPrdCnsTyp rep (PrdType typ) = RST.PrdCnsType PrdRep <$> lowerTyp rep typ
lowerPrdCnsTyp rep (CnsType typ) = RST.PrdCnsType CnsRep <$> lowerTyp (flipPolarityRep rep) typ

lowerBinOpChain :: PolarityRep pol -> Typ -> NonEmpty(Loc, BinOp, Typ) -> RenamerM (RST.Typ pol)
lowerBinOpChain rep fst rest = do
    op <- associateOps fst rest
    lowerTyp rep op

---------------------------------------------------------------------------------
-- Operator Desugaring
---------------------------------------------------------------------------------

desugaring :: Loc -> PolarityRep pol -> TyOpDesugaring -> Typ -> Typ -> RenamerM (RST.Typ pol)
desugaring loc PosRep UnionDesugaring tl tr = do
    tl <- lowerTyp PosRep tl
    tr <- lowerTyp PosRep tr
    case tl of
        RST.TySet loc rep k ts -> pure $ RST.TySet loc rep k (ts ++ [tr])
        _ -> pure $ RST.TySet loc PosRep Nothing [tl, tr]
desugaring loc NegRep UnionDesugaring _ _ =
    throwError (LowerError (Just loc) UnionInNegPolarity)
desugaring loc NegRep InterDesugaring tl tr = do
    tl <- lowerTyp NegRep tl
    tr <- lowerTyp NegRep tr
    case tl of
        RST.TySet loc rep k ts -> pure $ RST.TySet loc rep k (ts ++ [tr])
        _ -> pure $ RST.TySet loc NegRep Nothing [tl, tr]
desugaring loc PosRep InterDesugaring _ _ =
    throwError (LowerError (Just loc) IntersectionInPosPolarity)
desugaring loc rep (NominalDesugaring tyname) tl tr = do
    lowerTyp rep (TyNominal loc tyname [tl, tr])

lookupTyOp :: Loc -> BinOp -> RenamerM TyOp
lookupTyOp loc op = do
    tyops <- tyOps <$> getSymbolTable
    case find (\tyop -> symbol tyop == op) tyops of
      Nothing -> throwError (LowerError (Just loc) (UnknownOperator (ppPrint op)))
      Just tyop -> pure tyop

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
associateOps :: Typ -> NonEmpty (Loc, BinOp, Typ) -> RenamerM Typ
associateOps lhs ((loc, s, rhs) :| []) = pure $ TyBinOp loc lhs s rhs
associateOps lhs ((loc1, s1, rhs1) :| next@(loc2, s2, _rhs2) : rest) = do
    op1 <- lookupTyOp loc1 s1
    op2 <- lookupTyOp loc2 s2
    if (prec op2) > (prec op1) || (assoc op1 == RightAssoc)
    then do
        rhs <- associateOps rhs1 (next :| rest)
        pure $ TyBinOp loc1 lhs s1 rhs
    else if assoc op1 == LeftAssoc
    then do
        associateOps (TyBinOp loc1 lhs s1 rhs1) (next :| rest)
    else
        throwError (OtherError Nothing "Unhandled case reached. This is a bug the operator precedence parser")

lowerBinOp :: Loc -> PolarityRep pol -> Typ -> BinOp -> Typ -> RenamerM (RST.Typ pol)
lowerBinOp loc rep lhs s rhs = do
    op <- lookupTyOp loc s
    desugaring loc rep (desugar op) lhs rhs
