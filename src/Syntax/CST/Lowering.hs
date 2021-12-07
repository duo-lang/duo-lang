module Syntax.CST.Lowering where

import Data.Set qualified as S
import Data.List.NonEmpty (NonEmpty((:|)))

import Syntax.CommonTerm
import qualified Syntax.Types as AST
import Syntax.Types (PolarityRep (PosRep, NegRep), flipPolarityRep, Polarity (Neg, Pos), freeTypeVars)
import Syntax.CST.Types

---------------------------------------------------------------------------------
-- Lowering & Polarization (CST -> AST)
---------------------------------------------------------------------------------

data LoweringError where
    -- Type scheme violations
    MissingVarsInTypeScheme :: LoweringError
    -- Polarity violations
    TopInPosPolarity :: LoweringError
    BotInNegPolarity :: LoweringError
    IntersectionInPosPolarity :: LoweringError
    UnionInNegPolarity :: LoweringError
    -- Operator errors
    UnknownOperator :: BinOp -> LoweringError

instance Show LoweringError where
    show MissingVarsInTypeScheme = "Missing declaration of type variable"
    show TopInPosPolarity = "Cannot use of `Top` in positive polarity"
    show BotInNegPolarity = "Cannot use of `Bot` in negative polarity"
    show IntersectionInPosPolarity = "Cannot use `/\\` in positive polarity"
    show UnionInNegPolarity = "Cannot use `\\/` in negative polarity"
    show (UnknownOperator op) = "Undefined type operator `" ++ show op ++ "`"

lowerTypeScheme :: PolarityRep pol -> TypeScheme -> Either LoweringError (AST.TypeScheme pol)
lowerTypeScheme rep (TypeScheme tvars monotype) = do
    monotype <- lowerTyp rep monotype
    if S.fromList (freeTypeVars monotype) `S.isSubsetOf` tvars
        then pure (AST.TypeScheme (S.toList tvars) monotype)
        else Left MissingVarsInTypeScheme

lowerTyp :: PolarityRep pol -> Typ -> Either LoweringError (AST.Typ pol)
lowerTyp rep (TyVar v) = pure $ AST.TyVar rep Nothing v
lowerTyp rep (TyXData AST.Data name sigs) = do
    sigs <- lowerXTorSigs rep sigs
    pure $ AST.TyData rep name sigs
lowerTyp rep (TyXData AST.Codata name sigs) = do
    sigs <- lowerXTorSigs (flipPolarityRep rep) sigs
    pure $ AST.TyCodata rep name sigs
lowerTyp rep (TyNominal name) = pure $ AST.TyNominal rep Nothing name
lowerTyp rep (TyRec v typ) = AST.TyRec rep v <$> lowerTyp rep typ
lowerTyp PosRep TyTop = Left TopInPosPolarity
lowerTyp NegRep TyTop = pure desugarTopType
lowerTyp PosRep TyBot = pure desugarBotType
lowerTyp NegRep TyBot = Left BotInNegPolarity
lowerTyp rep (TyBinOpChain fst rest) = lowerBinOpChain rep fst rest
lowerTyp rep (TyBinOp fst op snd) = lowerBinOp rep fst op snd
lowerTyp rep (TyParens typ) = lowerTyp rep typ

lowerXTorSigs :: PolarityRep pol -> [XtorSig] -> Either LoweringError [AST.XtorSig pol]
lowerXTorSigs rep sigs = sequence $ lowerXTorSig rep <$> sigs

lowerXTorSig :: PolarityRep pol -> XtorSig -> Either LoweringError (AST.XtorSig pol)
lowerXTorSig rep (MkXtorSig name ctx) = AST.MkXtorSig name <$> lowerLinearContext rep ctx

lowerLinearContext :: PolarityRep pol -> LinearContext -> Either LoweringError (AST.LinearContext pol)
lowerLinearContext rep ctx = sequence $ lowerPrdCnsTyp rep <$> ctx

lowerPrdCnsTyp :: PolarityRep pol -> PrdCnsTyp -> Either LoweringError (AST.PrdCnsType pol)
lowerPrdCnsTyp rep (PrdType typ) = AST.PrdType <$> lowerTyp rep typ
lowerPrdCnsTyp rep (CnsType typ) = AST.CnsType <$> lowerTyp (flipPolarityRep rep) typ

lowerBinOpChain :: PolarityRep pol -> Typ -> NonEmpty(BinOp, Typ) -> Either LoweringError (AST.Typ pol)
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
        desugar :: forall pol. PolarityRep pol -> Typ -> Typ -> Either LoweringError (AST.Typ pol)
    }

data Assoc = LeftAssoc | RightAssoc
    deriving Eq

type Ops = [Op]
type Prio = Int

ops :: Ops
ops = [
        Op FunOp RightAssoc desugarArrowType,
        Op UnionOp LeftAssoc desugarUnionType,
        Op InterOp LeftAssoc desugarIntersectionType
    ]

lookupOp :: Ops -> BinOp -> Either LoweringError (Op, Prio)
lookupOp = lookupHelper 0
    where
        lookupHelper :: Prio -> Ops -> BinOp -> Either LoweringError (Op, Prio)
        lookupHelper _ [] s = Left (UnknownOperator s)
        lookupHelper p (op@(Op s' _ _) : _) s | s == s' = Right (op, p)
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
associateOps :: Typ -> NonEmpty (BinOp, Typ) -> Either LoweringError Typ
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

lowerBinOp :: PolarityRep pol -> Typ -> BinOp -> Typ -> Either LoweringError (AST.Typ pol)
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

desugarIntersectionType :: PolarityRep pol -> Typ -> Typ -> Either LoweringError (AST.Typ pol)
desugarIntersectionType NegRep tl tr = do
    tl <- lowerTyp NegRep tl
    tr <- lowerTyp NegRep tr
    case tl of
        AST.TySet rep k ts -> pure $ AST.TySet rep k (ts ++ [tr])
        _ -> pure $ AST.TySet NegRep Nothing [tl, tr]
desugarIntersectionType PosRep _ _ = Left IntersectionInPosPolarity

desugarUnionType :: PolarityRep pol -> Typ -> Typ -> Either LoweringError (AST.Typ pol)
desugarUnionType PosRep tl tr = do
    tl <- lowerTyp PosRep tl
    tr <- lowerTyp PosRep tr
    case tl of
        AST.TySet rep k ts -> pure $ AST.TySet rep k (ts ++ [tr])
        _ -> pure $ AST.TySet PosRep Nothing [tl, tr]
desugarUnionType NegRep _ _ = Left UnionInNegPolarity

-- | Desugar function arrow syntax
desugarArrowType :: PolarityRep pol -> Typ -> Typ -> Either LoweringError (AST.Typ pol)
desugarArrowType PosRep tl tr = do
    tl <- lowerTyp (flipPolarityRep PosRep) tl
    tr <- lowerTyp PosRep tr
    pure $ AST.TyCodata PosRep Nothing
        [ AST.MkXtorSig (MkXtorName Structural "Ap")
          [AST.PrdType tl, AST.CnsType tr]]
desugarArrowType NegRep tl tr = do
    tl <- lowerTyp (flipPolarityRep NegRep) tl
    tr <- lowerTyp NegRep tr
    pure $ AST.TyCodata NegRep Nothing
        [ AST.MkXtorSig (MkXtorName Structural "Ap")
          [AST.PrdType tl, AST.CnsType tr]]
