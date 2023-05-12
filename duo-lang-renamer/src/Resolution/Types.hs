module Resolution.Types
    ( resolveTyp
    , resolveTypeScheme
    , resolveXTorSigs
    , resolveMethodSigs
    ) where

import Control.Monad.Except (throwError)
import Data.Set qualified as S
import Data.Text qualified as T
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M

import Errors.Renamer
import Resolution.Definition
import Resolution.SymbolTable
import Syntax.RST.Types qualified as RST
import Syntax.RST.Types (PolarityRep(..), flipPolarityRep)
import Syntax.RST.Names
import Syntax.CST.Types
import Syntax.CST.Program qualified as CST
import Syntax.CST.Names
import Loc (Loc(..), defaultLoc)
import Control.Monad.Reader (asks, MonadReader (local))

---------------------------------------------------------------------------------
-- Lowering & Polarization (CST -> RST)
---------------------------------------------------------------------------------

resolveTypeScheme :: PolarityRep pol -> TypeScheme -> ResolverM (RST.TypeScheme pol)
resolveTypeScheme rep ts = do
    monotype <- resolveTyp rep ts.monotype
    if RST.freeTVars monotype `S.isSubsetOf` S.fromList (map fst ts.vars)
    then pure (RST.TypeScheme ts.loc ts.vars monotype)
        else throwError (MissingVarsInTypeScheme ts.loc)

resolveTyp :: PolarityRep pol -> Typ -> ResolverM (RST.Typ pol)
resolveTyp rep (TySkolemVar loc v) = do
    recVars <- asks (\x -> x.rr_recVars)
    let vr = skolemToRecRVar v
    if vr `S.member` recVars
      then pure $ RST.TyRecVar loc rep vr
      else pure $ RST.TySkolemVar loc rep v

-- Nominal Data
resolveTyp rep (TyXData loc Data sigs) = do
    sigs <- resolveXTorSigs rep sigs
    pure $ RST.TyData loc rep sigs
-- Refinement Data
resolveTyp rep (TyXRefined loc Data tn argVars sigs) = do
    NominalResult tn' _ _ pknd <- lookupTypeConstructor loc tn
    sigs <- resolveXTorSigs rep sigs
    if length pknd.kindArgs /= length argVars then 
      throwError (UnknownResolutionError loc ("not enough bound skolem variables for "  <> T.pack (show tn)))
    else 
      pure $ RST.TyDataRefined loc rep pknd argVars tn' sigs
-- Nominal Codata
resolveTyp rep (TyXData loc Codata sigs) = do
    sigs <- resolveXTorSigs (flipPolarityRep rep) sigs
    pure $ RST.TyCodata loc rep sigs
-- Refinement Codata
resolveTyp rep (TyXRefined loc Codata tn argVars sigs) = do
    NominalResult tn' _ _ pknd <- lookupTypeConstructor loc tn
    sigs <- resolveXTorSigs (flipPolarityRep rep) sigs
    if length pknd.kindArgs /= length argVars then 
      throwError (UnknownResolutionError loc ("Not enough bound skolem variables for " <> T.pack (show tn)))
    else 
      pure $ RST.TyCodataRefined loc rep pknd argVars tn' sigs
resolveTyp rep (TyNominal loc name) = do
  res <- lookupTypeConstructor loc name
  case res of
    SynonymResult name' typ -> do
      typ' <- resolveTyp rep typ
      pure $ RST.TySyn loc rep name' typ'
    NominalResult rtn _ CST.Refined _ ->
      throwError (UnknownResolutionError loc ("Refined type " <> T.pack (show rtn) <> " cannot be used as a nominal type constructor."))
    NominalResult name' _ CST.NotRefined polyknd ->
      pure $ RST.TyNominal loc rep polyknd name'

--applied types 
resolveTyp rep (TyApp loc ty (Just tyn) args) = do 
  ty' <- resolveTyp rep ty 
  res <- lookupTypeConstructor loc tyn
  case res of 
    SynonymResult _ _ -> throwError (UnknownResolutionError loc "Type synonmys cannot be applied to arguments (yet)")
    NominalResult nm _ CST.Refined pknd -> do
      args' <- resolveArgs loc rep nm pknd args
      pure $ RST.TyApp loc rep ty' nm args'
    NominalResult nm _ CST.NotRefined pknd -> do 
      args' <- resolveArgs loc rep nm pknd args 
      pure $ RST.TyApp loc rep ty' nm args'
  where
    resolveArgs loc rep tyn pknd args = do
      args' <- resolveTypeArgs loc rep tyn.rnTnName pknd (NE.toList args)
      let args'' = case args' of [] -> error "can't happen"; (fst:rst) -> fst:|rst
      return args''

resolveTyp rep (TyApp loc ty Nothing args) = do 
  case ty of 
    TySkolemVar _ sk -> do 
      tynMap <- asks (\x -> x.rr_recVarTyNames) 
      case M.lookup sk tynMap of 
        Nothing -> throwError (UnknownResolutionError loc "Application of recursive variable outside of Nominal or Refinement Type")
        Just tyn -> resolveTyp rep (TyApp loc ty (Just tyn) args)
    _ -> do
      let tyn = getTypeName ty
      case tyn of 
        Nothing -> throwError (UnknownResolutionError loc "Applications only allowed for nominal and refinement types")
        Just tyn' -> resolveTyp rep (TyApp loc ty (Just tyn') args)
    
resolveTyp rep (TyRec loc v typ) = do
        let vr = skolemToRecRVar v
        let tyn = getTypeName typ
        case tyn of 
          Nothing -> local (\r -> r { rr_recVars = S.insert vr $ r.rr_recVars  } ) $ RST.TyRec loc rep vr <$> resolveTyp rep typ
          Just tyn' -> local (\r -> r { rr_recVars = S.insert vr $ r.rr_recVars, rr_recVarTyNames = M.insert v tyn' r.rr_recVarTyNames }) $ RST.TyRec loc rep vr <$> resolveTyp rep typ

-- Lattice types    
resolveTyp PosRep (TyTop loc) =
    throwError (TopInPosPolarity loc)
resolveTyp NegRep (TyTop loc) =
    pure $ RST.TyTop loc
resolveTyp PosRep (TyBot loc) =
    pure $ RST.TyBot loc
resolveTyp NegRep (TyBot loc) =
    throwError (BotInNegPolarity loc)
resolveTyp rep (TyBinOpChain fst rest) =
    resolveBinOpChain rep fst rest
resolveTyp rep (TyBinOp loc fst op snd) =
    resolveBinOp loc rep fst op snd
resolveTyp rep (TyParens _loc typ) =
    resolveTyp rep typ
resolveTyp rep (TyKindAnnot mk ty) = do
    ty' <- resolveTyp rep ty
    pure $ RST.TyKindAnnot mk ty'
resolveTyp rep (TyI64 loc) =
    pure $ RST.TyI64 loc rep
resolveTyp rep (TyF64 loc) =
    pure $ RST.TyF64 loc rep
resolveTyp rep (TyChar loc) =
    pure $ RST.TyChar loc rep
resolveTyp rep (TyString loc) =
    pure $ RST.TyString loc rep

resolveTypeArgs :: forall pol. Loc -> PolarityRep pol -> TypeName -> PolyKind -> [Typ] -> ResolverM [RST.VariantType pol]
resolveTypeArgs loc rep tn pk@MkPolyKind{} args = do
    if length args /= length pk.kindArgs  then
        throwError (UnknownResolutionError loc ("Type constructor " <> tn.unTypeName <> " must be fully applied"))
    else do
        let
            f :: ((Variance, SkolemTVar, MonoKind), Typ) -> ResolverM (RST.VariantType pol)
            f ((Covariant,_,_),ty) = RST.CovariantType <$> resolveTyp rep ty
            f ((Contravariant,_,_),ty) = RST.ContravariantType <$> resolveTyp (flipPolarityRep rep) ty
        mapM f (zip pk.kindArgs args)
resolveTypeArgs loc _ _ (KindVar _) _ = throwError (UnknownResolutionError loc "Kind Variables should not be in the program at this point")


resolveXTorSigs :: PolarityRep pol -> [XtorSig] -> ResolverM [RST.XtorSig pol]
resolveXTorSigs rep = mapM (resolveXTorSig rep)

resolveXTorSig :: PolarityRep pol -> XtorSig -> ResolverM (RST.XtorSig pol)
resolveXTorSig rep (MkXtorSig name ctx) = RST.MkXtorSig name <$> resolveLinearContext rep ctx

resolveMethodSigs :: PolarityRep pol -> [XtorSig] -> ResolverM [RST.MethodSig pol]
resolveMethodSigs rep = mapM (resolveMethodSig rep)

resolveMethodSig :: PolarityRep pol -> XtorSig -> ResolverM (RST.MethodSig pol)
resolveMethodSig rep (MkXtorSig name ctx) = RST.MkMethodSig (MkMethodName name.unXtorName) <$> resolveLinearContext rep ctx

resolveLinearContext :: PolarityRep pol -> LinearContext -> ResolverM (RST.LinearContext pol)
resolveLinearContext rep = mapM (resolvePrdCnsTyp rep)

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
    pure $ RST.TyUnion loc tl tr
desugaring loc NegRep UnionDesugaring _ _ =
    throwError (UnionInNegPolarity loc)
desugaring loc NegRep InterDesugaring tl tr = do
    tl <- resolveTyp NegRep tl
    tr <- resolveTyp NegRep tr
    pure $ RST.TyInter loc tl tr
desugaring loc PosRep InterDesugaring _ _ =
    throwError (IntersectionInPosPolarity loc)
desugaring loc rep (NominalDesugaring tyname) tl tr = do
    resolveTyp rep (TyApp loc (TyNominal loc tyname) (Just tyname) (tl:|[tr]))

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
    if op2.prec > op1.prec || (op1.assoc == RightAssoc)
    then do
        rhs <- associateOps rhs1 (next :| rest)
        pure $ TyBinOp loc1 lhs s1 rhs
    else if op1.assoc == LeftAssoc
    then do
        associateOps (TyBinOp loc1 lhs s1 rhs1) (next :| rest)
    else
        throwError (UnknownResolutionError defaultLoc "Unhandled case reached. This is a bug the operator precedence parser")

resolveBinOp :: Loc -> PolarityRep pol -> Typ -> BinOp -> Typ -> ResolverM (RST.Typ pol)
resolveBinOp loc rep lhs s rhs = do
    (_,op) <- lookupTyOp loc s
    desugaring loc rep op.desugar lhs rhs
