module Resolution.Types
    ( resolveTyp
    , resolveTypeScheme
    , resolveXTorSigs
    , resolveMethodSigs
    ) where

import Control.Monad.Except (throwError)
import Data.Set qualified as S
import Data.Text qualified as T
import Data.Map qualified as M
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.List.NonEmpty qualified as NE

import Errors.Renamer
import Resolution.Definition
import Resolution.SymbolTable
import Syntax.RST.Types qualified as RST
import Syntax.RST.Types (PolarityRep(..), flipPolarityRep)
import Syntax.CST.Types
import Syntax.CST.Program qualified as CST
import Syntax.CST.Kinds
import Syntax.CST.Names
import Loc (Loc(..), defaultLoc)
import Control.Monad.Reader (asks, MonadReader (local))

---------------------------------------------------------------------------------
-- Lowering & Polarization (CST -> RST)
---------------------------------------------------------------------------------

resolveTypeScheme :: PolarityRep pol -> TypeScheme -> ResolverM (RST.TypeScheme pol)
resolveTypeScheme rep ts = do
    monotype <- resolveTyp rep ts.ts_monotype
    if RST.freeTVars monotype `S.isSubsetOf` S.fromList (map fst ts.ts_vars)
    then pure (RST.TypeScheme ts.ts_loc ts.ts_vars monotype)
        else throwError (MissingVarsInTypeScheme ts.ts_loc)

resolveTyp :: PolarityRep pol -> Typ -> ResolverM (RST.Typ pol)
resolveTyp rep (TyUniVar loc v) =
    pure $ RST.TyUniVar loc rep v
resolveTyp rep (TySkolemVar loc v) = do
    recVars <- asks rr_recVars
    let vr = skolemToRecRVar v
    if vr `S.member` recVars
      then pure $ RST.TyRecVar loc rep vr
      else pure $ RST.TySkolemVar loc rep v

-- Nominal Data
resolveTyp rep (TyXData loc Data sigs) = do
    sigs <- resolveXTorSigs rep sigs
    pure $ RST.TyData loc rep sigs
-- Refinement Data
resolveTyp rep (TyXRefined loc Data tn mrv sigs) = do
    NominalResult tn' _ _ pknd <- lookupTypeConstructor loc tn
    if not (null (kindArgs pknd)) then throwError (UnknownResolutionError loc ("Type " <> T.pack (show tn) <> " was not fully applied"))
    else do
      case mrv of 
        Nothing -> do
          sigs <- resolveXTorSigs rep sigs
          pure $ RST.TyDataRefined loc rep pknd tn' Nothing sigs
        Just sk -> do
          let rv = skolemToRecRVar sk
          sigs <- local (\r -> r { rr_recVars = S.insert rv $ rr_recVars r  } ) $ resolveXTorSigs rep sigs
          return $ RST.TyDataRefined loc rep pknd tn' (Just rv) sigs 
-- Nominal Codata
resolveTyp rep (TyXData loc Codata sigs) = do
    sigs <- resolveXTorSigs (flipPolarityRep rep) sigs
    pure $ RST.TyCodata loc rep sigs
-- Refinement Codata
resolveTyp rep (TyXRefined loc Codata tn mrv sigs) = do
    NominalResult tn' _ _ pknd <- lookupTypeConstructor loc tn
    if not (null (kindArgs pknd)) then throwError (UnknownResolutionError loc ("Type " <> T.pack (show tn) <> " was not fully applied")) else do
      case mrv of 
        Nothing -> do
          sigs <- resolveXTorSigs (flipPolarityRep rep) sigs
          pure $ RST.TyCodataRefined loc rep pknd tn' Nothing sigs
        Just sk -> do 
          let rv = skolemToRecRVar sk
          sigs <- local (\r -> r { rr_ref_recVars = M.insert rv (tn,pknd) $ rr_ref_recVars r  } ) $ resolveXTorSigs (flipPolarityRep rep) sigs
          return $ RST.TyCodataRefined loc rep pknd tn' (Just rv) sigs 

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
resolveTyp rep (TyApp loc ty@(TyNominal _loc tyn) args) = do 
  res <- lookupTypeConstructor loc tyn
  case res of 
    SynonymResult _ _ -> throwError (UnknownResolutionError loc "Type synonmys cannot be applied to arguments (yet)")
    NominalResult rtn _ CST.Refined _ -> throwError (UnknownResolutionError loc ("Refined type " <> T.pack (show rtn) <> " cannot be used as a nominal type constructor"))
    NominalResult _tyn' _ CST.NotRefined polyknd -> do 
      ty' <- resolveTyp rep ty
      args' <- resolveTypeArgs loc rep tyn polyknd (NE.toList args)
      case args' of 
        [] -> pure ty'
        (fst:rst) -> pure $ RST.TyApp loc rep ty' (fst:|rst)

resolveTyp rep (TyApp loc (TySkolemVar loc' sk) args) = do
  recVars <- asks rr_ref_recVars
  let rv = skolemToRecRVar sk
  case M.lookup rv recVars of 
    Nothing -> throwError (UnknownResolutionError loc' "Types can't be applied to Skolem Variables")
    Just (tn,pknd) -> do 
      args'<- resolveTypeArgs loc rep tn pknd (NE.toList args)
      let args'' = case args' of [] -> error "can't happen"; (fst:rst) -> fst :| rst
      pure $ RST.TyApp loc rep (RST.TyRecVar loc' rep rv) args''

resolveTyp rep (TyApp loc (TyXRefined loc' Data tn mrv sigs) args) = do 
    NominalResult tn' _ _ pknd <- lookupTypeConstructor loc tn
    case mrv of 
      Nothing -> do
        sigs <- resolveXTorSigs rep sigs
        args' <- resolveTypeArgs loc rep tn pknd (NE.toList args)
        let args'' = case args' of [] -> error "can't happen"; (fst:rst) -> fst:|rst
        pure $ RST.TyApp loc rep (RST.TyDataRefined loc' rep pknd tn' Nothing sigs) args''
      Just sk -> do 
        let rv = skolemToRecRVar sk
        sigs <- local (\r -> r { rr_ref_recVars = M.insert rv (tn,pknd) $ rr_ref_recVars r  } ) $ resolveXTorSigs rep sigs
        args' <- resolveTypeArgs loc rep tn pknd (NE.toList args)
        let args'' = case args' of [] -> error "can't happen"; (fst:rst) -> fst:|rst
        return $ RST.TyApp loc rep (RST.TyDataRefined loc' rep pknd tn' (Just rv) sigs) args''

resolveTyp rep (TyApp loc (TyXRefined loc' Codata tn mrv sigs) args) = do 
    NominalResult tn' _ _ pknd <- lookupTypeConstructor loc tn
    case mrv of 
      Nothing -> do
        sigs <- resolveXTorSigs (flipPolarityRep rep) sigs
        args' <- resolveTypeArgs loc rep tn pknd (NE.toList args)
        let args'' = case args' of [] -> error "can't happen"; (fst:rst) -> fst:|rst
        pure $ RST.TyApp loc rep (RST.TyCodataRefined loc' rep pknd tn' Nothing sigs) args''
      Just sk -> do 
        let rv = skolemToRecRVar sk
        sigs <- local (\r -> r { rr_ref_recVars = M.insert rv (tn,pknd) $ rr_ref_recVars r  } ) $ resolveXTorSigs (flipPolarityRep rep) sigs
        args' <- resolveTypeArgs loc rep tn pknd (NE.toList args)
        let args'' = case args' of [] -> error "can't happen"; (fst:rst) -> fst:|rst
        return $ RST.TyApp loc rep (RST.TyCodataRefined loc' rep pknd tn' (Just rv) sigs) args''


  
resolveTyp rep (TyApp loc (TyKindAnnot mk ty) args) = do 
  resolved <-  resolveTyp rep (TyApp loc ty args)
  pure $ RST.TyKindAnnot mk resolved

resolveTyp rep (TyApp loc (TyParens _ ty) args) = resolveTyp rep (TyApp loc ty args)

resolveTyp _ (TyApp loc ty _) = throwError (UnknownResolutionError loc ("Types can only be applied to nominal and refinement types, was applied to\n" <> T.pack (show ty)))

resolveTyp rep (TyRec loc v typ) = do
        let vr = skolemToRecRVar v
        local (\r -> r { rr_recVars = S.insert vr $ rr_recVars r  } ) $ RST.TyRec loc rep vr <$> resolveTyp rep typ

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
        throwError (UnknownResolutionError loc ("Type constructor " <> unTypeName tn <> " must be fully applied"))
    else do
        let
            f :: ((Variance, SkolemTVar, MonoKind), Typ) -> ResolverM (RST.VariantType pol)
            f ((Covariant,_,_),ty) = RST.CovariantType <$> resolveTyp rep ty
            f ((Contravariant,_,_),ty) = RST.ContravariantType <$> resolveTyp (flipPolarityRep rep) ty
        sequence (f <$> zip pk.kindArgs args)
resolveTypeArgs loc _ _ (KindVar _) _ = throwError (UnknownResolutionError loc "Kind Variables should not be in the program at this point")


resolveXTorSigs :: PolarityRep pol -> [XtorSig] -> ResolverM [RST.XtorSig pol]
resolveXTorSigs rep sigs = sequence $ resolveXTorSig rep <$> sigs

resolveXTorSig :: PolarityRep pol -> XtorSig -> ResolverM (RST.XtorSig pol)
resolveXTorSig rep (MkXtorSig name ctx) = RST.MkXtorSig name <$> resolveLinearContext rep ctx

resolveMethodSigs :: PolarityRep pol -> [XtorSig] -> ResolverM [RST.MethodSig pol]
resolveMethodSigs rep sigs = sequence $ resolveMethodSig rep <$> sigs

resolveMethodSig :: PolarityRep pol -> XtorSig -> ResolverM (RST.MethodSig pol)
resolveMethodSig rep (MkXtorSig name ctx) = RST.MkMethodSig (MkMethodName $ unXtorName name) <$> resolveLinearContext rep ctx

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
    resolveTyp rep (TyApp loc (TyNominal loc tyname) (tl:|[tr]))

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
        throwError (UnknownResolutionError defaultLoc "Unhandled case reached. This is a bug the operator precedence parser")

resolveBinOp :: Loc -> PolarityRep pol -> Typ -> BinOp -> Typ -> ResolverM (RST.Typ pol)
resolveBinOp loc rep lhs s rhs = do
    (_,op) <- lookupTyOp loc s
    desugaring loc rep (desugar op) lhs rhs
