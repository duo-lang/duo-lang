module TypeInference.GenerateConstraints.Terms
  ( GenConstraints(..)
  , genConstraintsTermRecursive
  ) where

import Control.Monad.Reader
import Errors
import Data.List.NonEmpty (NonEmpty((:|)))
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Program qualified as TST
import Syntax.TST.Types qualified as TST
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Program qualified as Core
import Syntax.RST.Types qualified as RST
import Syntax.RST.Types (Polarity(..), PolarityRep(..))
import Syntax.RST.Program qualified as RST
import Syntax.CST.Names
import Syntax.RST.Names
import Syntax.RST.Kinds
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Kinds
import Translate.EmbedTST (EmbedTST(..))
import Pretty.Pretty

import TypeInference.GenerateConstraints.Definition
import TypeInference.GenerateConstraints.Kinds
import TypeInference.Constraints
import TypeInference.SolveConstraints (resolveInstanceAnnot)
import Loc
import TypeInference.Environment
import TypeInference.GenerateConstraints.Primitives (primOps)
import Syntax.RST.Program (ClassDeclaration(classdecl_kinds))
import Syntax.TST.Terms (Substitution(..))

---------------------------------------------------------------------------------------------
-- Substitutions and Linear Contexts
---------------------------------------------------------------------------------------------

instance GenConstraints Core.PrdCnsTerm TST.PrdCnsTerm where
  genConstraints :: Core.PrdCnsTerm
                 -> GenM TST.PrdCnsTerm
  genConstraints (Core.PrdTerm tm) = TST.PrdTerm <$> genConstraints tm
  genConstraints (Core.CnsTerm tm) = TST.CnsTerm <$> genConstraints tm

instance GenConstraints Core.Substitution TST.Substitution where
  genConstraints :: Core.Substitution
                 -> GenM TST.Substitution
  genConstraints = fmap MkSubstitution . mapM genConstraints . (\x -> x.unSubstitution)

genConstraintsCtxts :: TST.LinearContext Pos -> TST.LinearContext Neg -> ConstraintInfo -> GenM ()
genConstraintsCtxts ctx1 ctx2 info | length ctx1 /= length ctx2 = do
  loc <- asks ((\x -> x.location) . snd)
  throwGenError (LinearContextsUnequalLength loc info ctx1 ctx2)
genConstraintsCtxts [] [] _ = return ()

genConstraintsCtxts ((TST.PrdCnsType PrdRep ty1) : rest1) (TST.PrdCnsType PrdRep ty2 : rest2) info = do
  addConstraint $ SubType info ty1 ty2
  addConstraint $ KindEq KindConstraint (TST.getKind ty1) (TST.getKind ty2)
  genConstraintsCtxts rest1 rest2 info

genConstraintsCtxts ((TST.PrdCnsType CnsRep ty1) : rest1) (TST.PrdCnsType CnsRep ty2 : rest2) info = do
  addConstraint $ SubType info ty2 ty1
  addConstraint $ KindEq KindConstraint (TST.getKind ty1) (TST.getKind ty2)
  genConstraintsCtxts rest1 rest2 info

genConstraintsCtxts (TST.PrdCnsType PrdRep _:_) (TST.PrdCnsType CnsRep _:_) info = do
  loc <- asks ((\x -> x.location) . snd)
  throwGenError (LinearContextIncompatibleTypeMode loc Prd info)
genConstraintsCtxts (TST.PrdCnsType CnsRep _:_) (TST.PrdCnsType PrdRep _:_) info = do
  loc <- asks ((\x -> x.location) . snd)
  throwGenError (LinearContextIncompatibleTypeMode loc Cns info)
genConstraintsCtxts ctx1@[] ctx2@(_:_) info = do
  loc <- asks ((\x -> x.location) . snd)
  throwGenError (LinearContextsUnequalLength loc info ctx1 ctx2)
genConstraintsCtxts ctx1@(_:_) ctx2@[] info = do
  loc <- asks ((\x -> x.location) . snd)
  throwGenError (LinearContextsUnequalLength loc info ctx1 ctx2)

---------------------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------------------

-- | Generate the constraints for a given Term.
instance GenConstraints (Core.Term pc) (TST.Term pc) where
  genConstraints :: Core.Term pc
                 -> GenM (TST.Term pc)
  --
  -- Bound variables:
  --
  -- Bound variables can be looked up in the context.
  --
  genConstraints (Core.BoundVar loc rep idx) = do
    ty <- lookupContext loc rep idx
    return (TST.BoundVar loc rep ty idx)
  --
  -- Free variables:
  --
  -- Free variables can be looked up in the environment,
  -- where they correspond to typing schemes. This typing
  -- scheme has to be instantiated with fresh unification variables.
  --
  genConstraints (Core.FreeVar loc rep v) = do
    tys <- snd <$> lookupTerm loc rep v
    ty <- instantiateTypeScheme v loc tys
    return (TST.FreeVar loc rep ty v)
  --
  -- Structural Xtors:
  --
  genConstraints (Core.Xtor loc annot rep RST.Structural xt subst) = do
    inferredSubst <- genConstraints subst
    let substTypes = TST.getTypArgs inferredSubst
    case rep of
      PrdRep -> do
        let rstty = RST.TyData defaultLoc PosRep [RST.MkXtorSig xt (embedTST <$> substTypes)]
        tstty <- annotateKind rstty
        return $ TST.Xtor loc annot rep tstty RST.Structural xt inferredSubst
      CnsRep -> do 
        let rstty = RST.TyCodata defaultLoc NegRep [RST.MkXtorSig xt (embedTST <$> substTypes)]
        tstty <- annotateKind rstty
        return $ TST.Xtor loc annot rep tstty RST.Structural xt inferredSubst
  --
  -- Nominal Xtors
  --
  genConstraints (Core.Xtor loc annot rep (RST.Nominal _) xt subst) = do
    -- First we infer the types of the arguments.
    substInferred <- genConstraints subst
    let substTypes = TST.getTypArgs substInferred
    -- Secondly we look up the argument types of the xtor in the type declaration.
    decl <- lookupDataDecl loc xt
    xtorSig <- lookupXtorSig loc xt NegRep
    -- Generate fresh unification variables for type parameters
    (args, tyParamsMap) <- freshTVarsForTypeParams (prdCnsToPol rep) decl
    -- Substitute these for the type parameters in the constructor signature
    let sig_args' = TST.zonk TST.SkolemRep tyParamsMap xtorSig.sig_args
    -- Then we generate constraints between the inferred types of the substitution
    -- and the types we looked up, i.e. the types declared in the XtorSig.
    genConstraintsCtxts substTypes sig_args' (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
    let nomTy rep = TST.TyNominal defaultLoc rep decl.data_kind decl.data_name
    if length args /= length decl.data_kind.kindArgs then
      throwOtherError loc ["Nominal Type " <> ppPrint decl.data_name <> " was not fully applied"]
    else do
      let ty = case args of [] -> nomTy; (fst:rst) -> \rep -> TST.TyApp defaultLoc rep decl.data_kind.returnKind (nomTy rep) decl.data_name (fst:|rst)
      case rep of
        PrdRep -> return (TST.Xtor loc annot rep (ty PosRep) (RST.Nominal decl.data_name.rnTnName) xt substInferred)
        CnsRep -> return (TST.Xtor loc annot rep (ty NegRep) (RST.Nominal decl.data_name.rnTnName) xt substInferred)
  --
  -- Refinement Xtors
  --
  genConstraints (Core.Xtor loc annot rep RST.Refinement xt subst) = do
    -- First we infer the types of the arguments.
    substInferred <- genConstraints subst
    let substTypes = TST.getTypArgs substInferred
    -- Secondly we look up the argument types of the xtor in the type declaration.
    -- Since we infer refinement types, we have to look up the translated xtorSig.
    decl <- lookupDataDecl loc xt
    xtorSigUpper <- lookupXtorSigUpper loc xt
    -- generate Constraints for applied types (if there are any)
    (args, tyParamsMap) <- freshTVarsForTypeParams (prdCnsToPol rep) decl
    let sig_args' = TST.zonk TST.SkolemRep tyParamsMap xtorSigUpper.sig_args
    substTypes' <- mapM replaceUniVars (zip substTypes sig_args')
    -- Then we generate constraints between the inferred types of the substitution
    -- and the translations of the types we looked up, i.e. the types declared in the XtorSig.
    genConstraintsCtxts substTypes' sig_args' (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
    if length args /= length decl.data_kind.kindArgs then
      throwOtherError loc ["Refinement Type " <> ppPrint decl.data_name <> " was not fully applied"]
    else do
      let ty = case rep of 
                 PrdRep -> do
                   let refTy = TST.TyDataRefined   defaultLoc PosRep decl.data_kind decl.data_name [TST.MkXtorSig xt substTypes']
                   case args of
                     [] -> refTy 
                     (fst:rst) -> TST.TyApp defaultLoc PosRep decl.data_kind.returnKind refTy decl.data_name (fst:|rst) 
                 CnsRep -> do
                   let refTy = TST.TyCodataRefined defaultLoc NegRep decl.data_kind  decl.data_name [TST.MkXtorSig xt substTypes']
                   case args of 
                     [] -> refTy 
                     (fst:rst) -> TST.TyApp defaultLoc NegRep decl.data_kind.returnKind refTy decl.data_name (fst:|rst)
      return $ TST.Xtor loc annot rep ty RST.Refinement xt substInferred
  --
  -- Structural pattern and copattern matches:
  --
  genConstraints (Core.XCase loc annot rep RST.Structural cases) = do
    inferredCases <- forM cases (\(Core.MkCmdCase cmdcase_loc (Core.XtorPat loc xt args) cmdcase_cmd) -> do
                        -- Generate positive and negative unification variables for all variables
                        -- bound in the pattern.
                        xtor <- lookupStructuralXtor xt
                        let argKnds = map snd xtor.strxtordecl_arity
                        let tVarArgs = zipWith (curry (\ ((x, y), z) -> (x, y, monoToAnyKind z))) args argKnds
                        (uvarsPos, uvarsNeg) <- freshTVars tVarArgs
                        -- Check the command in the context extended with the positive unification variables
                        cmdInferred <- withContext uvarsPos (genConstraints cmdcase_cmd)
                        -- Return the negative unification variables in the returned type.
                        return (TST.MkCmdCase cmdcase_loc (Core.XtorPat loc xt args) cmdInferred, TST.MkXtorSig xt uvarsNeg))
    let xtors = snd <$> inferredCases
    case rep of
      -- The return type is a structural type consisting of a XtorSig for each case.
      PrdRep -> do 
        let rstty = RST.TyCodata defaultLoc PosRep (embedTST <$> xtors)
        tstty <- annotateKind rstty
        return $ TST.XCase loc annot rep tstty RST.Structural (fst <$> inferredCases)
      CnsRep -> do
        let rstty = RST.TyData defaultLoc NegRep (embedTST <$> xtors)
        tstty <- annotateKind rstty
        return $ TST.XCase loc annot rep tstty RST.Structural (fst <$> inferredCases)
  --
  -- Nominal pattern and copattern matches
  --
  genConstraints (Core.XCase loc _ _ (RST.Nominal _) []) =
    -- We know that empty matches cannot be parsed as nominal.
    -- It is therefore safe to pattern match on the head of the xtors in the other cases.
    throwGenError (EmptyNominalMatch loc)
  genConstraints (Core.XCase loc annot rep (RST.Nominal _) cases@(pmcase:_)) = do
    -- We lookup the data declaration based on the first pattern match case.
    decl <- lookupDataDecl loc (case pmcase.cmdcase_pat of (Core.XtorPat _ xt _) -> xt)
    -- We check that all cases in the pattern match belong to the type declaration.
    checkCorrectness loc ((\cs -> case cs.cmdcase_pat of Core.XtorPat _ xt _ -> xt) <$> cases) decl
    -- We check that all xtors in the type declaration are matched against.
    checkExhaustiveness loc ((\cs -> case cs.cmdcase_pat of Core.XtorPat _ xt _ -> xt) <$> cases) decl
    -- Generate fresh unification variables for type parameters
    (args, tyParamsMap) <- freshTVarsForTypeParams (prdCnsToPol rep) decl

    inferredCases <- forM cases (\(Core.MkCmdCase cmdcase_loc (Core.XtorPat loc' xt args) cmdcase_cmd) -> do
                    -- We lookup the types belonging to the xtor in the type declaration.
                    posTypes <- (\x -> x.sig_args) <$> lookupXtorSig loc xt PosRep
                    negTypes <- (\x -> x.sig_args) <$> lookupXtorSig loc xt NegRep
                    -- Substitute fresh unification variables for type parameters
                    let posTypes' = TST.zonk TST.SkolemRep tyParamsMap posTypes
                    let negTypes' = TST.zonk TST.SkolemRep tyParamsMap negTypes
                    -- We generate constraints for the command in the context extended
                    -- with the types from the signature.
                    cmdInferred <- withContext posTypes' (genConstraints cmdcase_cmd)
                    return (TST.MkCmdCase cmdcase_loc (Core.XtorPat loc' xt args) cmdInferred, TST.MkXtorSig xt negTypes'))
    let nomTy rep = TST.TyNominal defaultLoc rep decl.data_kind decl.data_name
    if length args /= length decl.data_kind.kindArgs then 
      throwOtherError loc ["Nominal Type " <> ppPrint decl.data_name <> " was not fully applied"]
    else do 
      let ty = case args of [] -> nomTy; (fst:rst) -> \rep -> TST.TyApp defaultLoc rep decl.data_kind.returnKind (nomTy rep) decl.data_name (fst:|rst)
      case rep of
        PrdRep -> return $ TST.XCase loc annot rep (ty PosRep) (RST.Nominal decl.data_name.rnTnName) (fst <$> inferredCases)
        CnsRep -> return $ TST.XCase loc annot rep (ty NegRep) (RST.Nominal decl.data_name.rnTnName) (fst <$> inferredCases)
  --
  -- Refinement pattern and copattern matches
  --
  genConstraints (Core.XCase loc _ _ RST.Refinement []) =
    -- We know that empty matches cannot be parsed as Refinement.
    -- It is therefore safe to pattern match on the head of the xtors in the other cases.
    throwGenError (EmptyRefinementMatch loc)
  genConstraints (Core.XCase loc annot rep RST.Refinement cases@(pmcase:_)) = do
    -- We lookup the data declaration based on the first pattern match case.
    decl <- lookupDataDecl loc (case pmcase.cmdcase_pat of (Core.XtorPat _ xt _) -> xt)
    -- We check that all cases in the pattern match belong to the type declaration.
    checkCorrectness loc ((\cs -> case cs.cmdcase_pat of Core.XtorPat _ xt _ -> xt) <$> cases) decl
    inferredCases <- forM cases (\(Core.MkCmdCase cmdcase_loc (Core.XtorPat loc xt args) cmdcase_cmd) -> do
                        -- Generate positive and negative unification variables for all variables
                        -- bound in the pattern.
                        xtor <- lookupXtorSig loc xt RST.PosRep
                        let argKnds = map TST.getKind xtor.sig_args
                        let tVarArgs = zipWith (curry (\ ((x, y), z) -> (x, y, z))) args argKnds
                        (uvarsPos, uvarsNeg) <- freshTVars tVarArgs
                        -- Check the command in the context extended with the positive unification variables
                        cmdInferred <- withContext uvarsPos (genConstraints cmdcase_cmd)
                        -- We have to bound the unification variables with the lower and upper bounds generated
                        -- from the information in the type declaration. These lower and upper bounds correspond
                        -- to the least and greatest type translation.
                        xtorLower <- lookupXtorSigLower loc xt
                        xtorUpper <- lookupXtorSigUpper loc xt 
                        let lowerBound' = xtorLower.sig_args
                        let upperBound' = xtorUpper.sig_args
                        uvarsNeg' <- mapM replaceUniVars (zip uvarsNeg lowerBound')
                        uvarsPos' <- mapM replaceUniVars (zip uvarsPos upperBound')
                        genConstraintsCtxts lowerBound' uvarsNeg' (PatternMatchConstraint loc)
                        genConstraintsCtxts uvarsPos' upperBound' (PatternMatchConstraint loc)
                        -- For the type, we return the unification variables which are now bounded by the least
                        -- and greatest type translation.
                        return (TST.MkCmdCase cmdcase_loc (Core.XtorPat loc xt args) cmdInferred, TST.MkXtorSig xt uvarsNeg'))
    -- Generate fresh unification variables for type parameters
    (argsPos, tyParamsMapPos) <- freshTVarsForTypeParams PosRep decl
    (argsNeg, tyParamsMapNeg) <- freshTVarsForTypeParams NegRep decl
    case rep of
      CnsRep -> do
        if length argsNeg /= length decl.data_kind.kindArgs then 
          throwOtherError loc ["Refinement Type " <> ppPrint decl.data_name <> " was not fully applied"]
        else do 
          let xtors = TST.zonk TST.SkolemRep tyParamsMapNeg . snd <$> inferredCases
          let refTy = TST.TyDataRefined defaultLoc NegRep decl.data_kind decl.data_name xtors
          let ty = case argsNeg of [] -> refTy; (fst:rst) -> TST.TyApp defaultLoc NegRep decl.data_kind.returnKind refTy decl.data_name (fst:|rst)
          return $ TST.XCase loc annot rep ty RST.Refinement (fst <$> inferredCases)
      PrdRep -> do
        if length argsPos /= length decl.data_kind.kindArgs then
          throwOtherError loc ["Refinement Type " <> ppPrint decl.data_name <> " was not fully applied"]
        else do
          let xtors = TST.zonk TST.SkolemRep tyParamsMapPos . snd <$> inferredCases
          let refTy = TST.TyCodataRefined defaultLoc PosRep decl.data_kind decl.data_name xtors
          let ty = case argsPos of [] -> refTy; (fst:rst) -> TST.TyApp defaultLoc PosRep decl.data_kind.returnKind refTy decl.data_name (fst:|rst)
          return $ TST.XCase loc annot rep ty RST.Refinement (fst <$> inferredCases)
  --
  -- Mu and TildeMu abstractions:
  --
  genConstraints (Core.MuAbs loc annot PrdRep bs cmd) = do
    (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs)) Nothing
    cmdInferred <- withContext [TST.PrdCnsType CnsRep uvneg] (genConstraints cmd)
    return (TST.MuAbs loc annot PrdRep uvpos bs cmdInferred)
  genConstraints (Core.MuAbs loc annot CnsRep bs cmd) = do
    (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs)) Nothing
    cmdInferred <- withContext [TST.PrdCnsType PrdRep uvpos] (genConstraints cmd)
    return (TST.MuAbs loc annot CnsRep uvneg bs cmdInferred)
  genConstraints (Core.PrimLitI64 loc i) = pure $ TST.PrimLitI64 loc i
  genConstraints (Core.PrimLitF64 loc d) = pure $ TST.PrimLitF64 loc d
  genConstraints (Core.PrimLitChar loc d) = pure $ TST.PrimLitChar loc d
  genConstraints (Core.PrimLitString loc d) = pure $ TST.PrimLitString loc d

instance GenConstraints Core.Command TST.Command where
  genConstraints :: Core.Command -> GenM TST.Command
  genConstraints (Core.ExitSuccess loc) =
    pure (TST.ExitSuccess loc)
  genConstraints (Core.ExitFailure loc) =
    pure (TST.ExitFailure loc)
  genConstraints (Core.Jump loc fv) = do
    -- Ensure that the referenced command is in scope
    _ <- lookupCommand loc fv
    pure (TST.Jump loc fv)
  genConstraints (Core.Method loc mn cn Nothing subst) = do
    decl <- lookupClassDecl loc cn
    insertSkolemsClass decl
      -- fresh type var and subsitution for type class variable(s)
    (tyParamsMap, uvs) <- createMethodSubst loc decl
    negTypes <- lookupMethodType loc mn decl NegRep
    ctxtNeg <- annotateKind negTypes
    let negTypes' = TST.zonk TST.SkolemRep tyParamsMap ctxtNeg 
    -- infer arg types
    substInferred <- genConstraints subst
    let substTypes = TST.getTypArgs substInferred
    genConstraintsCtxts substTypes negTypes' (TypeClassConstraint loc)
    case uvs of
      [] -> throwGenError (NoParamTypeClass loc)
      [uv] -> pure (TST.Method loc mn cn (TST.InstanceUnresolved uv) Nothing substInferred)
      _ -> throwGenError (MultiParamTypeClass loc)
  genConstraints (Core.Method loc mn cn (Just ty) subst) = do
    decl <- lookupClassDecl loc cn
    insertSkolemsClass decl
    case decl.classdecl_kinds.kindArgs of
      [] -> throwGenError (NoParamTypeClass loc)
      [(var, _, _)] -> do
        -- let resolvedType = (resolveType k typ, resolveType k tyn)
        resolvedType <- annotateKind ty
        -- generate kind constraints
        let tyParamsMap = paramsMap decl.classdecl_kinds.kindArgs [resolvedType]
        negTypes <- lookupMethodType loc mn decl NegRep
        ctxtNeg <- annotateKind negTypes
        let negTypes' = TST.zonk TST.SkolemRep tyParamsMap ctxtNeg 
        -- infer arg types
        substInferred <- genConstraints subst
        let substTypes = TST.getTypArgs substInferred
        genConstraintsCtxts substTypes negTypes' (TypeClassConstraint loc)
        env <- asks fst
        case var of
          Covariant -> case resolveInstanceAnnot PosRep (fst resolvedType) cn env of
            Right (inst,_,_) -> pure (TST.Method loc mn cn (TST.InstanceResolved inst) (Just resolvedType) substInferred)
            Left err -> throwGenError (InstanceResolution loc err)
          Contravariant -> case resolveInstanceAnnot NegRep (snd resolvedType) cn env of
            Right (inst,_,_) -> pure (TST.Method loc mn cn (TST.InstanceResolved inst) (Just resolvedType) substInferred)
            Left err -> throwGenError (InstanceResolution loc err)
      _ -> throwGenError (MultiParamTypeClass loc)
  genConstraints (Core.Print loc prd cmd) = do
    prd' <- genConstraints prd
    cmd' <- genConstraints cmd
    pure (TST.Print loc prd' cmd')
  genConstraints (Core.Read loc cns) = do
    cns' <- genConstraints cns
    peanoDecl <- lookupTypeName loc peanoNm
    let peanoKnd = peanoDecl.data_kind
    let cnsTy = TST.getTypeTerm cns'
    addConstraint (SubType (ReadConstraint loc)  (TST.TyNominal defaultLoc PosRep peanoKnd peanoNm) cnsTy)
    addConstraint $ KindEq KindConstraint (MkPknd peanoKnd) (TST.getKind cnsTy)
    return (TST.Read loc cns')
  genConstraints (Core.Apply loc annot t1 t2) = do
    t1' <- genConstraints t1
    t2' <- genConstraints t2
    let ty1 = TST.getTypeTerm t1'
    let ty2 = TST.getTypeTerm t2'
    addConstraint (SubType (CommandConstraint loc) ty1 ty2)
    addConstraint $ KindEq KindConstraint (TST.getKind ty1) (TST.getKind ty2)
    pure (TST.Apply loc annot (TST.getKind ty1) t1' t2')

  genConstraints (Core.PrimOp loc op subst) = do
    substInferred <- genConstraints subst
    let substTypes = TST.getTypArgs substInferred
    let sig = primOps op 
    sigs <- mapM annotateKind sig
    _ <- genConstraintsCtxts substTypes sigs (PrimOpArgsConstraint loc)
    pure (TST.PrimOp loc op substInferred)
  
instance GenConstraints Core.InstanceDeclaration TST.InstanceDeclaration where
  genConstraints :: Core.InstanceDeclaration -> GenM TST.InstanceDeclaration
  genConstraints idecl = do
    -- We lookup the class declaration  of the instance.
    cdecl <- lookupClassDecl idecl.instancedecl_loc idecl.instancedecl_class
    insertSkolemsClass cdecl
    -- We check that all implementations belong to the same type class.
    checkInstanceCoverage idecl.instancedecl_loc cdecl ((\(Core.XtorPat _ xt _) -> MkMethodName xt.unXtorName) . (\x -> x.instancecase_pat) <$> idecl.instancedecl_cases) 
    -- Generate fresh unification variables for type parameters
    instancety <- annotateKind idecl.instancedecl_typ
    let tyParamsMap = paramsMap cdecl.classdecl_kinds.kindArgs [instancety] 
    inferredCases <- forM idecl.instancedecl_cases (\(Core.MkInstanceCase instancecase_loc (Core.XtorPat loc xt args) instancecase_cmd) -> do
                    let mn :: MethodName = MkMethodName xt.unXtorName
                    -- We lookup the types belonging to the xtor in the type declaration.
                    posTypes <- lookupMethodType instancecase_loc mn cdecl PosRep
                    negTypes <- lookupMethodType instancecase_loc mn cdecl NegRep  
                    ctxtPos <- annotateKind posTypes
                    ctxtNeg <- annotateKind negTypes
                    -- Substitute fresh unification variables for type parameters
                    let posTypes' = TST.zonk TST.SkolemRep tyParamsMap ctxtPos 
                    let negTypes' = TST.zonk TST.SkolemRep tyParamsMap ctxtNeg 
                    -- We generate constraints for the command in the context extended
                    -- with the types from the signature.
                    cmdInferred <- withContext posTypes' (genConstraints instancecase_cmd)
                    genConstraintsCtxts posTypes' negTypes' (InstanceConstraint instancecase_loc)
                    pure TST.MkInstanceCase { instancecase_loc = instancecase_loc
                                            , instancecase_pat = Core.XtorPat loc xt args
                                            , instancecase_cmd = cmdInferred
                                            })
    pure TST.MkInstanceDeclaration { instancedecl_loc = idecl.instancedecl_loc
                                   , instancedecl_doc = idecl.instancedecl_doc
                                   , instancedecl_name = idecl.instancedecl_name
                                   , instancedecl_class = idecl.instancedecl_class
                                   , instancedecl_typ = instancety
                                   , instancedecl_cases = inferredCases
                                   }



---------------------------------------------------------------------------------------------
-- Checking recursive terms
---------------------------------------------------------------------------------------------

genConstraintsTermRecursive :: ModuleName
                            -> Loc
                            -> FreeVarName
                            -> PrdCnsRep pc -> Core.Term pc
                            -> GenM (TST.Term pc)
genConstraintsTermRecursive mn loc fv PrdRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv) Nothing
  tm <- withTerm mn PrdRep fv (TST.FreeVar loc PrdRep x fv) loc (TST.TypeScheme loc [] x) (genConstraints tm)
  let xTy = TST.getTypeTerm tm
  addConstraint (SubType RecursionConstraint xTy y)
  addConstraint $ KindEq KindConstraint (TST.getKind xTy) (TST.getKind y)
  return tm
genConstraintsTermRecursive mn loc fv CnsRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv) Nothing
  tm <- withTerm mn CnsRep fv (TST.FreeVar loc CnsRep y fv) loc (TST.TypeScheme loc [] y) (genConstraints tm)
  let yTy = TST.getTypeTerm tm
  addConstraint (SubType RecursionConstraint x yTy)
  addConstraint $ KindEq KindConstraint (TST.getKind x) (TST.getKind yTy)
  return tm
