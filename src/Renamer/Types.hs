module Renamer.Types (renameTyp, renameTypeScheme, renameXTorSig) where

import Control.Monad.Except (throwError)
import Data.Set qualified as S
import Data.List.NonEmpty (NonEmpty((:|)))

import Errors
import Renamer.Definition
import Renamer.SymbolTable
import Syntax.Common
import qualified Syntax.RST.Types as RST
import Syntax.RST.Types ( freeTVars )
import Syntax.CST.Types
import Utils (Loc(..))

---------------------------------------------------------------------------------
-- Lowering & Polarization (CST -> RST)
---------------------------------------------------------------------------------

renameTypeScheme :: PolarityRep pol -> TypeScheme -> RenamerM (RST.TypeScheme pol)
renameTypeScheme rep (TypeScheme { ts_loc, ts_vars, ts_monotype }) = do
    monotype <- renameTyp rep ts_monotype
    if (freeTVars monotype) `S.isSubsetOf` (S.fromList ts_vars)
        then pure (RST.TypeScheme ts_loc ts_vars monotype)
        else throwError (LowerError (Just ts_loc) MissingVarsInTypeScheme)

renameTyp :: PolarityRep pol -> Typ -> RenamerM (RST.Typ pol)
renameTyp rep (TyVar loc v) =
    pure $ RST.TyVar loc rep Nothing v
-- Nominal Data
renameTyp rep (TyXData loc Data Nothing sigs) = do
    sigs <- renameXTorSigs rep sigs
    pure $ RST.TyData loc rep Nothing sigs
-- Refinement Data
renameTyp rep (TyXData loc Data (Just tn) sigs) = do
    (tn',_) <- lookupTypeConstructor loc tn
    sigs <- renameXTorSigs rep sigs
    pure $ RST.TyData loc rep (Just tn') sigs
-- Nominal Codata
renameTyp rep (TyXData loc Codata Nothing sigs) = do
    sigs <- renameXTorSigs (flipPolarityRep rep) sigs
    pure $ RST.TyCodata loc rep Nothing sigs
-- Refinement Codata
renameTyp rep (TyXData loc Codata (Just tn) sigs) = do
    (tn',_) <- lookupTypeConstructor loc tn
    sigs <- renameXTorSigs (flipPolarityRep rep) sigs
    pure $ RST.TyCodata loc rep (Just tn') sigs
renameTyp rep (TyNominal loc name args) = do
    res <- lookupTypeConstructor loc name
    case res of
        (name', SynonymResult typ) -> case args of
            [] -> do
                typ' <- renameTyp rep typ
                pure $ RST.TySyn loc rep name' typ'
            _ -> throwError (OtherError (Just loc) "Type synonyms cannot be applied to arguments (yet).")
        (_, NominalResult _ Refined _) -> do
            throwError (OtherError (Just loc) "Refined type cannot be used as a nominal type constructor.")
        (name', NominalResult _ NotRefined polykind) -> do
            args' <- renameTypeArgs loc rep name polykind args
            pure $ RST.TyNominal loc rep Nothing name' args'
renameTyp rep (TyRec loc v typ) =
    RST.TyRec loc rep v <$> renameTyp rep typ
-- Lattice types    
renameTyp PosRep (TyTop loc) =
    throwError (LowerError (Just loc) TopInPosPolarity)
renameTyp NegRep (TyTop loc) =
    pure $ RST.TyTop loc Nothing
renameTyp PosRep (TyBot loc) =
    pure $ RST.TyBot loc Nothing
renameTyp NegRep (TyBot loc) =
    throwError (LowerError (Just loc) BotInNegPolarity)
renameTyp rep (TyBinOpChain fst rest) =
    renameBinOpChain rep fst rest
renameTyp rep (TyBinOp loc fst op snd) =
    renameBinOp loc rep fst op snd
renameTyp rep (TyParens _loc typ) =
    renameTyp rep typ
renameTyp rep (TyPrim loc pt) =
    pure $ RST.TyPrim loc rep pt



renameTypeArgs :: forall pol. Loc -> PolarityRep pol -> TypeName -> PolyKind -> [Typ] -> RenamerM [RST.VariantType pol]
renameTypeArgs loc rep tn (MkPolyKind { kindArgs }) args = do
    if (length args) /= length kindArgs  then
        throwError (OtherError (Just loc) ("Type constructor " <> unTypeName tn <> " must be fully applied"))
    else do
        let
            f :: ((Variance, TVar, MonoKind), Typ) -> RenamerM (RST.VariantType pol)
            f ((Covariant,_,_),ty) = RST.CovariantType <$> renameTyp rep ty
            f ((Contravariant,_,_),ty) = RST.ContravariantType <$> renameTyp (flipPolarityRep rep) ty
        sequence (f <$> zip kindArgs args)
        

renameXTorSigs :: PolarityRep pol -> [XtorSig] -> RenamerM [RST.XtorSig pol]
renameXTorSigs rep sigs = sequence $ renameXTorSig rep <$> sigs

renameXTorSig :: PolarityRep pol -> XtorSig -> RenamerM (RST.XtorSig pol)
renameXTorSig rep (MkXtorSig name ctx) = RST.MkXtorSig name <$> renameLinearContext rep ctx

renameLinearContext :: PolarityRep pol -> LinearContext -> RenamerM (RST.LinearContext pol)
renameLinearContext rep ctx = sequence $ renamePrdCnsTyp rep <$> ctx

renamePrdCnsTyp :: PolarityRep pol -> PrdCnsTyp -> RenamerM (RST.PrdCnsType pol)
renamePrdCnsTyp rep (PrdType typ) = RST.PrdCnsType PrdRep <$> renameTyp rep typ
renamePrdCnsTyp rep (CnsType typ) = RST.PrdCnsType CnsRep <$> renameTyp (flipPolarityRep rep) typ

renameBinOpChain :: PolarityRep pol -> Typ -> NonEmpty(Loc, BinOp, Typ) -> RenamerM (RST.Typ pol)
renameBinOpChain rep fst rest = do
    op <- associateOps fst rest
    renameTyp rep op

---------------------------------------------------------------------------------
-- Operator Desugaring
---------------------------------------------------------------------------------

desugaring :: Loc -> PolarityRep pol -> TyOpDesugaring -> Typ -> Typ -> RenamerM (RST.Typ pol)
desugaring loc PosRep UnionDesugaring tl tr = do
    tl <- renameTyp PosRep tl
    tr <- renameTyp PosRep tr
    pure $ RST.TyUnion loc Nothing tl tr
desugaring loc NegRep UnionDesugaring _ _ =
    throwError (LowerError (Just loc) UnionInNegPolarity)
desugaring loc NegRep InterDesugaring tl tr = do
    tl <- renameTyp NegRep tl
    tr <- renameTyp NegRep tr
    pure $ RST.TyInter loc Nothing tl tr
desugaring loc PosRep InterDesugaring _ _ =
    throwError (LowerError (Just loc) IntersectionInPosPolarity)
desugaring loc rep (NominalDesugaring tyname) tl tr = do
    renameTyp rep (TyNominal loc tyname [tl, tr])

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
    (_,op1) <- lookupTyOp loc1 s1
    (_,op2) <- lookupTyOp loc2 s2
    if (prec op2) > (prec op1) || (assoc op1 == RightAssoc)
    then do
        rhs <- associateOps rhs1 (next :| rest)
        pure $ TyBinOp loc1 lhs s1 rhs
    else if assoc op1 == LeftAssoc
    then do
        associateOps (TyBinOp loc1 lhs s1 rhs1) (next :| rest)
    else
        throwError (OtherError Nothing "Unhandled case reached. This is a bug the operator precedence parser")

renameBinOp :: Loc -> PolarityRep pol -> Typ -> BinOp -> Typ -> RenamerM (RST.Typ pol)
renameBinOp loc rep lhs s rhs = do
    (_,op) <- lookupTyOp loc s
    desugaring loc rep (desugar op) lhs rhs
