module Renamer.Types (lowerTyp, lowerTypeScheme, lowerXTorSig) where

import Control.Monad.Except (throwError)
import Data.Set qualified as S
import Data.Text qualified as T
import Data.List.NonEmpty (NonEmpty((:|)))

import Errors
import Renamer.Definition
import Syntax.Common
import qualified Syntax.AST.Types as AST
import Syntax.AST.Types ( freeTypeVars)
import Syntax.CST.Types
import Data.List

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
lowerTyp rep (TyVar v) = pure $ AST.TyVar rep Nothing v
lowerTyp rep (TyXData Data name sigs) = do
    sigs <- lowerXTorSigs rep sigs
    pure $ AST.TyData rep name sigs
lowerTyp rep (TyXData Codata name sigs) = do
    sigs <- lowerXTorSigs (flipPolarityRep rep) sigs
    pure $ AST.TyCodata rep name sigs
lowerTyp rep (TyNominal name args) = do
    (conArgs, covArgs) <- lowerTypeArgs rep name args
    pure $ AST.TyNominal rep Nothing name conArgs covArgs
lowerTyp rep (TyRec v typ) = AST.TyRec rep v <$> lowerTyp rep typ
lowerTyp PosRep TyTop = throwError (LowerError Nothing TopInPosPolarity)
lowerTyp NegRep TyTop = pure desugarTopType
lowerTyp PosRep TyBot = pure desugarBotType
lowerTyp NegRep TyBot = throwError (LowerError Nothing BotInNegPolarity)
lowerTyp rep (TyBinOpChain fst rest) = lowerBinOpChain rep fst rest
lowerTyp rep (TyBinOp fst op snd) = lowerBinOp rep fst op snd
lowerTyp rep (TyParens typ) = lowerTyp rep typ
lowerTyp rep (TyPrim pt) = pure $ AST.TyPrim rep pt

lowerTypeArgs :: PolarityRep pol -> TypeName -> [Typ] -> RenamerM ([AST.Typ (FlipPol pol)], [AST.Typ pol])
lowerTypeArgs rep tn args = do
    MkPolyKind { contravariant, covariant } <- lookupTypeConstructorAritiy tn
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

lowerBinOpChain :: PolarityRep pol -> Typ -> NonEmpty(BinOp, Typ) -> RenamerM (AST.Typ pol)
lowerBinOpChain rep fst rest = do
    op <- associateOps fst rest
    lowerTyp rep op

---------------------------------------------------------------------------------
-- Operator Desugaring
---------------------------------------------------------------------------------

data TyOpDesugaring where
    UnionDesugaring :: TyOpDesugaring
    InterDesugaring :: TyOpDesugaring
    NominalDesugaring :: TypeName -> TyOpDesugaring

desugaring :: PolarityRep pol -> TyOpDesugaring -> Typ -> Typ -> RenamerM (AST.Typ pol)
desugaring PosRep UnionDesugaring tl tr = do
    tl <- lowerTyp PosRep tl
    tr <- lowerTyp PosRep tr
    case tl of
        AST.TySet rep k ts -> pure $ AST.TySet rep k (ts ++ [tr])
        _ -> pure $ AST.TySet PosRep Nothing [tl, tr]
desugaring NegRep UnionDesugaring _ _ =
    throwError (LowerError Nothing UnionInNegPolarity)
desugaring NegRep InterDesugaring tl tr = do
    tl <- lowerTyp NegRep tl
    tr <- lowerTyp NegRep tr
    case tl of
        AST.TySet rep k ts -> pure $ AST.TySet rep k (ts ++ [tr])
        _ -> pure $ AST.TySet NegRep Nothing [tl, tr]
desugaring PosRep InterDesugaring _ _ =
    throwError (LowerError Nothing IntersectionInPosPolarity)
desugaring rep (NominalDesugaring tyname) tl tr = do
    lowerTyp rep (TyNominal tyname [tl, tr])

data TyOp = MkTyOp
    {
        symbol :: BinOp,
        prec :: Precedence,
        assoc :: Associativity,
        desugar :: TyOpDesugaring
    }




-- | Type operator for the function type
functionTyOp :: TyOp
functionTyOp = MkTyOp
  { symbol = CustomOp (MkTyOpName "->")
  , prec = MkPrecedence 0
  , assoc = RightAssoc
  , desugar = NominalDesugaring (MkTypeName "Fun")
  }

-- | Type operator for the union type
unionTyOp :: TyOp
unionTyOp = MkTyOp
  { symbol = UnionOp
  , prec = MkPrecedence 1
  , assoc = LeftAssoc
  , desugar = UnionDesugaring
  }

-- | Type operator for the intersection type
interTyOp :: TyOp
interTyOp = MkTyOp
  { symbol = InterOp
  , prec = MkPrecedence 2
  , assoc = LeftAssoc
  , desugar = InterDesugaring
  }

-- | Type operator for the Par type
parTyOp :: TyOp
parTyOp = MkTyOp
  { symbol = CustomOp (MkTyOpName "⅋")
  , prec = MkPrecedence 3
  , assoc = LeftAssoc
  , desugar = NominalDesugaring (MkTypeName "Par")
  }

tyops :: [TyOp]
tyops = [ functionTyOp, unionTyOp, interTyOp, parTyOp ]

lookupTyOp :: BinOp -> RenamerM TyOp
lookupTyOp op = case find (\tyop -> symbol tyop == op) tyops of
    Nothing -> throwError (LowerError Nothing (UnknownOperator (T.pack (show op))))
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
associateOps :: Typ -> NonEmpty (BinOp, Typ) -> RenamerM Typ
associateOps lhs ((s, rhs) :| []) = pure $ TyBinOp lhs s rhs
associateOps lhs ((s1, rhs1) :| next@(s2, _rhs2) : rest) = do
    op1 <- lookupTyOp s1
    op2 <- lookupTyOp s2
    if (prec op2) > (prec op1) || (assoc op1 == RightAssoc)
    then do
        rhs <- associateOps rhs1 (next :| rest)
        pure $ TyBinOp lhs s1 rhs
    else if assoc op1 == LeftAssoc
    then do
        associateOps (TyBinOp lhs s1 rhs1) (next :| rest)
    else
        throwError (OtherError Nothing "Unhandled case reached. This is a bug the operator precedence parser")

lowerBinOp :: PolarityRep pol -> Typ -> BinOp -> Typ -> RenamerM (AST.Typ pol)
lowerBinOp rep lhs s rhs = do
    op <- lookupTyOp s
    desugaring rep (desugar op) lhs rhs

---------------------------------------------------------------------------------
-- Syntactic Sugar
---------------------------------------------------------------------------------

desugarTopType :: AST.Typ 'Neg
desugarTopType = AST.TySet NegRep Nothing []

desugarBotType :: AST.Typ 'Pos
desugarBotType = AST.TySet PosRep Nothing []
