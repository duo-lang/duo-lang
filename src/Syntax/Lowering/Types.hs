module Syntax.Lowering.Types (lowerTyp, lowerTypeScheme, lowerXTorSig) where

import Control.Monad.Except (throwError)
import Data.Set qualified as S
import Data.Text qualified as T
import Data.List.NonEmpty (NonEmpty((:|)))

import Errors
import Syntax.Lowering.Lowering
import Syntax.CommonTerm
import qualified Syntax.AST.Types as AST
import Syntax.AST.Types (PolarityRep (PosRep, NegRep), flipPolarityRep, Polarity (Neg, Pos), freeTypeVars)
import Syntax.CST.Types

---------------------------------------------------------------------------------
-- Lowering & Polarization (CST -> AST)
---------------------------------------------------------------------------------



lowerTypeScheme :: PolarityRep pol -> TypeScheme -> LowerM (AST.TypeScheme pol)
lowerTypeScheme rep (TypeScheme tvars monotype) = do
    monotype <- lowerTyp rep monotype
    if S.fromList (freeTypeVars monotype) `S.isSubsetOf` (S.fromList tvars)
        then pure (AST.TypeScheme tvars monotype)
        else throwError (LowerError Nothing MissingVarsInTypeScheme)

lowerTyp :: PolarityRep pol -> Typ -> LowerM (AST.Typ pol)
lowerTyp rep (TyVar v) = pure $ AST.TyVar rep Nothing v
lowerTyp rep (TyXData AST.Data name sigs) = do
    sigs <- lowerXTorSigs rep sigs
    pure $ AST.TyData rep name sigs
lowerTyp rep (TyXData AST.Codata name sigs) = do
    sigs <- lowerXTorSigs (flipPolarityRep rep) sigs
    pure $ AST.TyCodata rep name sigs
lowerTyp rep (TyNominal name) = pure $ AST.TyNominal rep Nothing name
lowerTyp rep (TyRec v typ) = AST.TyRec rep v <$> lowerTyp rep typ
lowerTyp PosRep TyTop = throwError (LowerError Nothing TopInPosPolarity)
lowerTyp NegRep TyTop = pure desugarTopType
lowerTyp PosRep TyBot = pure desugarBotType
lowerTyp NegRep TyBot = throwError (LowerError Nothing BotInNegPolarity)
lowerTyp rep (TyBinOpChain fst rest) = lowerBinOpChain rep fst rest
lowerTyp rep (TyBinOp fst op snd) = lowerBinOp rep fst op snd
lowerTyp rep (TyParens typ) = lowerTyp rep typ

lowerXTorSigs :: PolarityRep pol -> [XtorSig] -> LowerM [AST.XtorSig pol]
lowerXTorSigs rep sigs = sequence $ lowerXTorSig rep <$> sigs

lowerXTorSig :: PolarityRep pol -> XtorSig -> LowerM (AST.XtorSig pol)
lowerXTorSig rep (MkXtorSig name ctx) = AST.MkXtorSig name <$> lowerLinearContext rep ctx

lowerLinearContext :: PolarityRep pol -> LinearContext -> LowerM (AST.LinearContext pol)
lowerLinearContext rep ctx = sequence $ lowerPrdCnsTyp rep <$> ctx

lowerPrdCnsTyp :: PolarityRep pol -> PrdCnsTyp -> LowerM (AST.PrdCnsType pol)
lowerPrdCnsTyp rep (PrdType typ) = AST.PrdCnsType PrdRep <$> lowerTyp rep typ
lowerPrdCnsTyp rep (CnsType typ) = AST.PrdCnsType CnsRep <$> lowerTyp (flipPolarityRep rep) typ

lowerBinOpChain :: PolarityRep pol -> Typ -> NonEmpty(BinOp, Typ) -> LowerM (AST.Typ pol)
lowerBinOpChain rep fst rest = do
    op <- associateOps fst rest
    lowerTyp rep op

---------------------------------------------------------------------------------
-- Operator Desugaring
---------------------------------------------------------------------------------

data Op = Op
    {
        symbol :: BinOp,
        assoc :: Assoc,
        desugar :: forall pol. PolarityRep pol -> Typ -> Typ -> LowerM (AST.Typ pol)
    }

data Assoc = LeftAssoc | RightAssoc
    deriving Eq

type Ops = [Op]
type Prio = Int

funOp :: Op
funOp = Op { symbol = FunOp, assoc = RightAssoc, desugar = desugarArrowType }

unionOp :: Op
unionOp = Op { symbol = UnionOp, assoc = LeftAssoc, desugar =  desugarUnionType }

interOp :: Op
interOp = Op { symbol = InterOp, assoc = LeftAssoc, desugar = desugarIntersectionType }

parOp :: Op
parOp = Op { symbol = ParOp, assoc = LeftAssoc, desugar = desugarParType }

ops :: Ops
ops = [ funOp, unionOp, interOp, parOp ]

lookupOp :: Ops -> BinOp -> LowerM (Op, Prio)
lookupOp = lookupHelper 0
    where
        lookupHelper :: Prio -> Ops -> BinOp -> LowerM (Op, Prio)
        lookupHelper _ [] s = throwError (LowerError Nothing (UnknownOperator (T.pack (show s))))
        lookupHelper p (op@(Op s' _ _) : _) s | s == s' = pure (op, p)
        lookupHelper p (_ : ops) s = lookupHelper (p + 1) ops s

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
associateOps :: Typ -> NonEmpty (BinOp, Typ) -> LowerM Typ
associateOps lhs ((s, rhs) :| []) = pure $ TyBinOp lhs s rhs
associateOps lhs ((s1, rhs1) :| next@(s2, _rhs2) : rest) = do
    (op1, prio1) <- lookupOp ops s1
    (_op2, prio2) <- lookupOp ops s2
    if prio2 > prio1 || (assoc op1 == RightAssoc)
    then do
        rhs <- associateOps rhs1 (next :| rest)
        pure $ TyBinOp lhs s1 rhs
    else if assoc op1 == LeftAssoc
    then do
        associateOps (TyBinOp lhs s1 rhs1) (next :| rest)
    else
        error "Unhandled case reached. This is a bug the operator precedence parser"

lowerBinOp :: PolarityRep pol -> Typ -> BinOp -> Typ -> LowerM (AST.Typ pol)
lowerBinOp rep lhs s rhs = do
    (op, _) <- lookupOp ops s
    desugar op rep lhs rhs

---------------------------------------------------------------------------------
-- Syntactic Sugar
---------------------------------------------------------------------------------

desugarTopType :: AST.Typ 'Neg
desugarTopType = AST.TySet NegRep Nothing []

desugarBotType :: AST.Typ 'Pos
desugarBotType = AST.TySet PosRep Nothing []

desugarIntersectionType :: PolarityRep pol -> Typ -> Typ -> LowerM (AST.Typ pol)
desugarIntersectionType NegRep tl tr = do
    tl <- lowerTyp NegRep tl
    tr <- lowerTyp NegRep tr
    case tl of
        AST.TySet rep k ts -> pure $ AST.TySet rep k (ts ++ [tr])
        _ -> pure $ AST.TySet NegRep Nothing [tl, tr]
desugarIntersectionType PosRep _ _ = throwError (LowerError Nothing IntersectionInPosPolarity)

desugarUnionType :: PolarityRep pol -> Typ -> Typ -> LowerM (AST.Typ pol)
desugarUnionType PosRep tl tr = do
    tl <- lowerTyp PosRep tl
    tr <- lowerTyp PosRep tr
    case tl of
        AST.TySet rep k ts -> pure $ AST.TySet rep k (ts ++ [tr])
        _ -> pure $ AST.TySet PosRep Nothing [tl, tr]
desugarUnionType NegRep _ _ = throwError (LowerError Nothing UnionInNegPolarity)

-- | Desugar function arrow syntax
desugarArrowType :: PolarityRep pol -> Typ -> Typ -> LowerM (AST.Typ pol)
desugarArrowType PosRep tl tr = do
    tl <- lowerTyp (flipPolarityRep PosRep) tl
    tr <- lowerTyp PosRep tr
    pure $ AST.TyCodata PosRep Nothing
        [ AST.MkXtorSig (MkXtorName Structural "Ap")
          [AST.PrdCnsType PrdRep tl, AST.PrdCnsType CnsRep tr]]
desugarArrowType NegRep tl tr = do
    tl <- lowerTyp (flipPolarityRep NegRep) tl
    tr <- lowerTyp NegRep tr
    pure $ AST.TyCodata NegRep Nothing
        [ AST.MkXtorSig (MkXtorName Structural "Ap")
          [AST.PrdCnsType PrdRep tl, AST.PrdCnsType CnsRep tr]]

desugarParType :: PolarityRep pol -> Typ -> Typ -> LowerM (AST.Typ pol)
desugarParType PosRep tl tr = do
    tl <- lowerTyp PosRep tl
    tr <- lowerTyp PosRep tr
    pure $ AST.TyCodata PosRep Nothing [ AST.MkXtorSig (MkXtorName Structural "Par") [AST.PrdCnsType CnsRep tl, AST.PrdCnsType CnsRep tr]]
desugarParType NegRep tl tr = do
    tl <- lowerTyp NegRep tl
    tr <- lowerTyp NegRep tr
    pure $ AST.TyCodata NegRep Nothing [ AST.MkXtorSig (MkXtorName Structural "Par") [AST.PrdCnsType CnsRep tl, AST.PrdCnsType CnsRep tr]]