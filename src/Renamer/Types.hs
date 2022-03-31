module Renamer.Types (lowerTyp, lowerTypeScheme, lowerXTorSig) where

import Control.Monad.Except (throwError)
import Data.Set qualified as S
import Data.List.NonEmpty (NonEmpty((:|)))

import Errors
import Pretty.Pretty
import Renamer.Definition
import Renamer.SymbolTable
import Syntax.Common
import qualified Syntax.AST.Types as AST
import Syntax.AST.Types ( freeTypeVars)
import Syntax.CST.Types
import Data.List
import Utils (Loc(..))

---------------------------------------------------------------------------------
-- Lowering & Polarization (CST -> AST)
---------------------------------------------------------------------------------

lowerTypeScheme :: PolarityRep pol -> TypeScheme -> RenamerM (AST.TypeScheme pol)
lowerTypeScheme rep (TypeScheme tvars monotype) = do
    monotype <- lowerTyp rep monotype
    if S.fromList (freeTypeVars monotype) `S.isSubsetOf` (S.fromList tvars)
        then pure (AST.TypeScheme tvars monotype)
        else throwError (LowerError Nothing MissingVarsInTypeScheme)

lowerTyp :: PolarityRep pol -> Typ -> RenamerM (AST.Typ pol)
lowerTyp rep (TyVar _loc v) = pure $ AST.TyVar rep Nothing v
lowerTyp rep (TyXData _loc Data name sigs) = do
    sigs <- lowerXTorSigs rep sigs
    pure $ AST.TyData rep name sigs
lowerTyp rep (TyXData _loc Codata name sigs) = do
    sigs <- lowerXTorSigs (flipPolarityRep rep) sigs
    pure $ AST.TyCodata rep name sigs
lowerTyp rep (TyNominal loc name args) = do
    (conArgs, covArgs) <- lowerTypeArgs loc rep name args
    pure $ AST.TyNominal rep Nothing name conArgs covArgs
lowerTyp rep (TyRec _loc v typ) = AST.TyRec rep v <$> lowerTyp rep typ
lowerTyp PosRep (TyTop loc) = throwError (LowerError (Just loc) TopInPosPolarity)
lowerTyp NegRep (TyTop _loc) = pure desugarTopType
lowerTyp PosRep (TyBot _loc) = pure desugarBotType
lowerTyp NegRep (TyBot loc) = throwError (LowerError (Just loc) BotInNegPolarity)
lowerTyp rep (TyBinOpChain fst rest) = lowerBinOpChain rep fst rest
lowerTyp rep (TyBinOp loc fst op snd) = lowerBinOp loc rep fst op snd
lowerTyp rep (TyParens _loc typ) = lowerTyp rep typ
lowerTyp rep (TyPrim _loc pt) = pure $ AST.TyPrim rep pt

lowerTypeArgs :: Loc -> PolarityRep pol -> TypeName -> [Typ] -> RenamerM ([AST.Typ (FlipPol pol)], [AST.Typ pol])
lowerTypeArgs loc rep tn args = do
    MkPolyKind { contravariant, covariant } <- lookupTypeConstructorAritiy loc tn
    let (contra, cov) = splitAt (length contravariant) args
    if (length contravariant) /= length contra || (length covariant) /= length cov then
        throwOtherError ["Type constructor " <> unTypeName tn <> " must be fully applied"]
    else do
        contra <- sequence (lowerTyp (flipPolarityRep rep) <$> contra)
        cov <- sequence (lowerTyp rep <$> cov)
        pure (contra, cov)

lowerXTorSigs :: PolarityRep pol -> [XtorSig] -> RenamerM [AST.XtorSig pol]
lowerXTorSigs rep sigs = sequence $ lowerXTorSig rep <$> sigs

lowerXTorSig :: PolarityRep pol -> XtorSig -> RenamerM (AST.XtorSig pol)
lowerXTorSig rep (MkXtorSig name ctx) = AST.MkXtorSig name <$> lowerLinearContext rep ctx

lowerLinearContext :: PolarityRep pol -> LinearContext -> RenamerM (AST.LinearContext pol)
lowerLinearContext rep ctx = sequence $ lowerPrdCnsTyp rep <$> ctx

lowerPrdCnsTyp :: PolarityRep pol -> PrdCnsTyp -> RenamerM (AST.PrdCnsType pol)
lowerPrdCnsTyp rep (PrdType typ) = AST.PrdCnsType PrdRep <$> lowerTyp rep typ
lowerPrdCnsTyp rep (CnsType typ) = AST.PrdCnsType CnsRep <$> lowerTyp (flipPolarityRep rep) typ

lowerBinOpChain :: PolarityRep pol -> Typ -> NonEmpty(Loc, BinOp, Typ) -> RenamerM (AST.Typ pol)
lowerBinOpChain rep fst rest = do
    op <- associateOps fst rest
    lowerTyp rep op

---------------------------------------------------------------------------------
-- Operator Desugaring
---------------------------------------------------------------------------------

desugaring :: Loc -> PolarityRep pol -> TyOpDesugaring -> Typ -> Typ -> RenamerM (AST.Typ pol)
desugaring _loc PosRep UnionDesugaring tl tr = do
    tl <- lowerTyp PosRep tl
    tr <- lowerTyp PosRep tr
    case tl of
        AST.TySet rep k ts -> pure $ AST.TySet rep k (ts ++ [tr])
        _ -> pure $ AST.TySet PosRep Nothing [tl, tr]
desugaring loc NegRep UnionDesugaring _ _ =
    throwError (LowerError (Just loc) UnionInNegPolarity)
desugaring _loc NegRep InterDesugaring tl tr = do
    tl <- lowerTyp NegRep tl
    tr <- lowerTyp NegRep tr
    case tl of
        AST.TySet rep k ts -> pure $ AST.TySet rep k (ts ++ [tr])
        _ -> pure $ AST.TySet NegRep Nothing [tl, tr]
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

lowerBinOp :: Loc -> PolarityRep pol -> Typ -> BinOp -> Typ -> RenamerM (AST.Typ pol)
lowerBinOp loc rep lhs s rhs = do
    op <- lookupTyOp loc s
    desugaring loc rep (desugar op) lhs rhs

---------------------------------------------------------------------------------
-- Syntactic Sugar
---------------------------------------------------------------------------------

desugarTopType :: AST.Typ 'Neg
desugarTopType = AST.TySet NegRep Nothing []

desugarBotType :: AST.Typ 'Pos
desugarBotType = AST.TySet PosRep Nothing []
