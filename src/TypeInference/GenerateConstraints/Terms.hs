module TypeInference.GenerateConstraints.Terms
  ( GenConstraints(..)
  , genConstraintsTermRecursive
  ) where

import Control.Monad.Reader
import Errors
import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Program qualified as TST
import Syntax.TST.Types qualified as TST
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Program qualified as Core
import Syntax.RST.Types qualified as RST
import Syntax.RST.Types (Polarity(..), PolarityRep(..))
import Syntax.CST.Names
import Syntax.CST.Kinds
import Translate.EmbedTST (EmbedTST(..))

import TypeInference.GenerateConstraints.Definition
import TypeInference.GenerateConstraints.Kinds
import TypeInference.Constraints
import Loc
import Lookup
import TypeInference.GenerateConstraints.Primitives (primOps)
import Syntax.RST.Program (ClassDeclaration(classdecl_kinds))

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
  genConstraints = mapM genConstraints

genConstraintsCtxts :: TST.LinearContext Pos -> TST.LinearContext Neg -> ConstraintInfo -> GenM ()
genConstraintsCtxts ctx1 ctx2 info | length ctx1 /= length ctx2 = do
  loc <- asks (location . snd)
  throwGenError (LinearContextsUnequalLength loc info ctx1 ctx2)
genConstraintsCtxts [] [] _ = return ()
genConstraintsCtxts ((TST.PrdCnsType PrdRep ty1) : rest1) (TST.PrdCnsType PrdRep ty2 : rest2) info = do
  addConstraint $ SubType info ty1 ty2
  genConstraintsCtxts rest1 rest2 info
genConstraintsCtxts ((TST.PrdCnsType CnsRep ty1) : rest1) (TST.PrdCnsType CnsRep ty2 : rest2) info = do
  addConstraint $ SubType info ty2 ty1
  genConstraintsCtxts rest1 rest2 info
genConstraintsCtxts (TST.PrdCnsType PrdRep _:_) (TST.PrdCnsType CnsRep _:_) info = do
  loc <- asks (location . snd)
  throwGenError (LinearContextIncompatibleTypeMode loc Prd info)
genConstraintsCtxts (TST.PrdCnsType CnsRep _:_) (TST.PrdCnsType PrdRep _:_) info = do
  loc <- asks (location . snd)
  throwGenError (LinearContextIncompatibleTypeMode loc Cns info)
genConstraintsCtxts ctx1@[] ctx2@(_:_) info = do
  loc <- asks (location . snd)
  throwGenError (LinearContextsUnequalLength loc info ctx1 ctx2)
genConstraintsCtxts ctx1@(_:_) ctx2@[] info = do
  loc <- asks (location . snd)
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
  genConstraints (Core.Xtor loc annot rep CST.Structural xt subst) = do
    inferredSubst <- genConstraints subst
    let substTypes = TST.getTypArgs inferredSubst
    case rep of
      PrdRep -> do
        let rstty = RST.TyData defaultLoc PosRep [RST.MkXtorSig xt (embedTST <$> substTypes)]
        tstty <- annotateKind rstty
        return $ TST.Xtor loc annot rep tstty CST.Structural xt inferredSubst
      CnsRep -> do 
        let rstty = RST.TyCodata defaultLoc NegRep [RST.MkXtorSig xt (embedTST <$> substTypes)]
        tstty <- annotateKind rstty
        return $ TST.Xtor loc annot rep tstty CST.Structural xt inferredSubst
  --
  -- Nominal Xtors
  --
  genConstraints (Core.Xtor loc annot rep CST.Nominal xt subst) = do
    -- First we infer the types of the arguments.
    substInferred <- genConstraints subst
    let substTypes = TST.getTypArgs substInferred
    -- Secondly we look up the argument types of the xtor in the type declaration.
    decl <- lookupDataDecl loc xt
    xtorSig <- lookupXtorSig loc xt NegRep
    -- Generate fresh unification variables for type parameters
    (args, tyParamsMap) <- freshTVarsForTypeParams (prdCnsToPol rep) decl
    -- Substitute these for the type parameters in the constructor signature
    let sig_args' = TST.zonk TST.SkolemRep tyParamsMap (TST.sig_args xtorSig)
    -- Then we generate constraints between the inferred types of the substitution
    -- and the types we looked up, i.e. the types declared in the XtorSig.
    genConstraintsCtxts substTypes sig_args' (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
    knd <- getKindDecl decl
    case rep of
      PrdRep -> return (TST.Xtor loc annot rep (TST.TyNominal defaultLoc PosRep knd (TST.data_name decl) args) CST.Nominal xt substInferred)
      CnsRep -> return (TST.Xtor loc annot rep (TST.TyNominal defaultLoc NegRep knd (TST.data_name decl) args) CST.Nominal xt substInferred)
  --
  -- Refinement Xtors
  --
  genConstraints (Core.Xtor loc annot rep CST.Refinement xt subst) = do
    -- First we infer the types of the arguments.
    substInferred <- genConstraints subst
    let substTypes = TST.getTypArgs substInferred
    -- Secondly we look up the argument types of the xtor in the type declaration.
    -- Since we infer refinement types, we have to look up the translated xtorSig.
    decl <- lookupDataDecl loc xt
    xtorSigUpper <- lookupXtorSigUpper loc xt
    -- Then we generate constraints between the inferred types of the substitution
    -- and the translations of the types we looked up, i.e. the types declared in the XtorSig.
    genConstraintsCtxts substTypes (TST.sig_args xtorSigUpper) (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
    knd <- getKindDecl decl
    case rep of
      PrdRep -> return (TST.Xtor loc annot rep (TST.TyDataRefined   defaultLoc PosRep knd (TST.data_name decl) [TST.MkXtorSig xt substTypes]) CST.Refinement xt substInferred)
      CnsRep -> return (TST.Xtor loc annot rep (TST.TyCodataRefined defaultLoc NegRep knd (TST.data_name decl) [TST.MkXtorSig xt substTypes]) CST.Refinement xt substInferred)
  --
  -- Structural pattern and copattern matches:
  --
  genConstraints (Core.XCase loc annot rep CST.Structural cases) = do
    inferredCases <- forM cases (\Core.MkCmdCase{ cmdcase_pat = Core.XtorPat loc xt args, cmdcase_loc, cmdcase_cmd} -> do
                        -- Generate positive and negative unification variables for all variables
                        -- bound in the pattern.
                        (uvarsPos, uvarsNeg) <- freshTVars args
                        -- Check the command in the context extended with the positive unification variables
                        cmdInferred <- withContext uvarsPos (genConstraints cmdcase_cmd)
                        -- Return the negative unification variables in the returned type.
                        return (TST.MkCmdCase cmdcase_loc (TST.XtorPat loc xt args) cmdInferred, TST.MkXtorSig xt uvarsNeg))
    let xtors = snd <$> inferredCases
    case rep of
      -- The return type is a structural type consisting of a XtorSig for each case.
      PrdRep -> do 
        let rstty = RST.TyCodata defaultLoc PosRep (embedTST <$> xtors)
        tstty <- annotateKind rstty
        return $ TST.XCase loc annot rep tstty CST.Structural (fst <$> inferredCases)
      CnsRep -> do
        let rstty = RST.TyData defaultLoc NegRep (embedTST <$> xtors)
        tstty <- annotateKind rstty
        return $ TST.XCase loc annot rep tstty CST.Structural (fst <$> inferredCases)
  --
  -- Nominal pattern and copattern matches
  --
  genConstraints (Core.XCase loc _ _ CST.Nominal []) =
    -- We know that empty matches cannot be parsed as nominal.
    -- It is therefore safe to pattern match on the head of the xtors in the other cases.
    throwGenError (EmptyNominalMatch loc)
  genConstraints (Core.XCase loc annot rep CST.Nominal cases@(pmcase:_)) = do
    -- We lookup the data declaration based on the first pattern match case.
    decl <- lookupDataDecl loc (case Core.cmdcase_pat pmcase of (Core.XtorPat _ xt _) -> xt)
    -- We check that all cases in the pattern match belong to the type declaration.
    checkCorrectness loc ((\cs -> case Core.cmdcase_pat cs of Core.XtorPat _ xt _ -> xt) <$> cases) decl
    -- We check that all xtors in the type declaration are matched against.
    checkExhaustiveness loc ((\cs -> case Core.cmdcase_pat cs of Core.XtorPat _ xt _ -> xt) <$> cases) decl
    -- Generate fresh unification variables for type parameters
    (args, tyParamsMap) <- freshTVarsForTypeParams (prdCnsToPol rep) decl

    inferredCases <- forM cases (\Core.MkCmdCase {cmdcase_loc, cmdcase_pat = Core.XtorPat loc' xt args, cmdcase_cmd} -> do
                    -- We lookup the types belonging to the xtor in the type declaration.
                    posTypes <- TST.sig_args <$> lookupXtorSig loc xt PosRep
                    negTypes <- TST.sig_args <$> lookupXtorSig loc xt NegRep
                    -- Substitute fresh unification variables for type parameters
                    let posTypes' = TST.zonk TST.SkolemRep tyParamsMap posTypes
                    let negTypes' = TST.zonk TST.SkolemRep tyParamsMap negTypes
                    -- We generate constraints for the command in the context extended
                    -- with the types from the signature.
                    cmdInferred <- withContext posTypes' (genConstraints cmdcase_cmd)
                    return (TST.MkCmdCase cmdcase_loc (TST.XtorPat loc' xt args) cmdInferred, TST.MkXtorSig xt negTypes'))
    knd <- getKindDecl decl
    case rep of
      PrdRep -> return $ TST.XCase loc annot rep (TST.TyNominal defaultLoc PosRep knd (TST.data_name decl) args) CST.Nominal (fst <$> inferredCases)
      CnsRep -> return $ TST.XCase loc annot rep (TST.TyNominal defaultLoc NegRep knd (TST.data_name decl) args) CST.Nominal (fst <$> inferredCases)
  --
  -- Refinement pattern and copattern matches
  --
  genConstraints (Core.XCase loc _ _ CST.Refinement []) =
    -- We know that empty matches cannot be parsed as Refinement.
    -- It is therefore safe to pattern match on the head of the xtors in the other cases.
    throwGenError (EmptyRefinementMatch loc)
  genConstraints (Core.XCase loc annot rep CST.Refinement cases@(pmcase:_)) = do
    -- We lookup the data declaration based on the first pattern match case.
    decl <- lookupDataDecl loc (case Core.cmdcase_pat pmcase of (Core.XtorPat _ xt _) -> xt)
    -- We check that all cases in the pattern match belong to the type declaration.
    checkCorrectness loc ((\cs -> case Core.cmdcase_pat cs of Core.XtorPat _ xt _ -> xt) <$> cases) decl
    inferredCases <- forM cases (\Core.MkCmdCase {cmdcase_loc, cmdcase_pat = Core.XtorPat loc xt args , cmdcase_cmd} -> do
                        -- Generate positive and negative unification variables for all variables
                        -- bound in the pattern.
                        (uvarsPos, uvarsNeg) <- freshTVars args
                        -- Check the command in the context extended with the positive unification variables
                        cmdInferred <- withContext uvarsPos (genConstraints cmdcase_cmd)
                        -- We have to bound the unification variables with the lower and upper bounds generated
                        -- from the information in the type declaration. These lower and upper bounds correspond
                        -- to the least and greatest type translation.
                        xtorLower <- lookupXtorSigLower loc xt
                        xtorUpper <- lookupXtorSigUpper loc xt 
                        let lowerBound' = TST.sig_args xtorLower
                        let upperBound' = TST.sig_args xtorUpper
                        genConstraintsCtxts lowerBound' uvarsNeg (PatternMatchConstraint loc)
                        genConstraintsCtxts uvarsPos upperBound' (PatternMatchConstraint loc)
                        -- For the type, we return the unification variables which are now bounded by the least
                        -- and greatest type translation.
                        return (TST.MkCmdCase cmdcase_loc (TST.XtorPat loc xt args) cmdInferred, TST.MkXtorSig xt uvarsNeg))
    knd <- getKindDecl decl
    case rep of
      PrdRep -> return $ TST.XCase loc annot rep (TST.TyCodataRefined defaultLoc PosRep knd (TST.data_name decl) (snd <$> inferredCases)) CST.Refinement (fst <$> inferredCases)
      CnsRep -> return $ TST.XCase loc annot rep (TST.TyDataRefined   defaultLoc NegRep knd (TST.data_name decl) (snd <$> inferredCases)) CST.Refinement (fst <$> inferredCases)
  --
  -- Mu and TildeMu abstractions:
  --
  genConstraints (Core.MuAbs loc annot PrdRep bs cmd) = do
    (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
    cmdInferred <- withContext [TST.PrdCnsType CnsRep uvneg] (genConstraints cmd)
    return (TST.MuAbs loc annot PrdRep uvpos bs cmdInferred)
  genConstraints (Core.MuAbs loc annot CnsRep bs cmd) = do
    (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
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
  genConstraints (Core.Method loc mn cn subst) = do
    decl <- lookupClassDecl loc cn
      -- fresh type var and subsitution for type class variable(s)
    tyParamsMap <- createMethodSubst loc decl
    negTypes <- lookupMethodType loc mn decl NegRep
    ctxtNeg <- annotateKind negTypes
    let negTypes' = TST.zonk TST.SkolemRep tyParamsMap ctxtNeg 
    -- infer arg types
    substInferred <- genConstraints subst
    let substTypes = TST.getTypArgs substInferred
    genConstraintsCtxts substTypes negTypes' (TypeClassConstraint loc)
    pure (TST.Method loc mn cn substInferred)
  genConstraints (Core.Print loc prd cmd) = do
    prd' <- genConstraints prd
    cmd' <- genConstraints cmd
    pure (TST.Print loc prd' cmd')
  genConstraints (Core.Read loc cns) = do
    cns' <- genConstraints cns
    peanoDecl <- lookupTypeName loc peanoNm
    let peanoKnd = CBox (returnKind (TST.data_kind peanoDecl))
    addConstraint (SubType (ReadConstraint loc)  (TST.TyNominal defaultLoc PosRep peanoKnd peanoNm []) (TST.getTypeTerm cns'))
    return (TST.Read loc cns')
  genConstraints (Core.Apply loc annot t1 t2) = do
    t1' <- genConstraints t1
    t2' <- genConstraints t2
    let ty1 = TST.getTypeTerm t1'
    let ty2 = TST.getTypeTerm t2'
    addConstraint (SubType (CommandConstraint loc) ty1 ty2)
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
  genConstraints Core.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases } = do
    -- We lookup the class declaration  of the instance.
    decl <- lookupClassDecl instancedecl_loc instancedecl_name
    -- We check that all implementations belong to the same type class.
    checkInstanceCoverage instancedecl_loc decl ((\(Core.XtorPat _ xt _) -> MkMethodName $ unXtorName xt) . Core.instancecase_pat <$> instancedecl_cases) 
    -- Generate fresh unification variables for type parameters
    instancety <- annotateKind instancedecl_typ
    let tyParamsMap = paramsMap (classdecl_kinds decl) [instancety] 
    inferredCases <- forM instancedecl_cases (\Core.MkInstanceCase { instancecase_loc, instancecase_pat = Core.XtorPat loc xt args, instancecase_cmd } -> do
                    let mn :: MethodName = MkMethodName $ unXtorName xt
                    -- We lookup the types belonging to the xtor in the type declaration.
                    posTypes <- lookupMethodType instancecase_loc mn decl PosRep
                    negTypes <- lookupMethodType instancecase_loc mn decl NegRep
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
    pure TST.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                                  , instancedecl_doc = instancedecl_doc
                                  , instancedecl_name = instancedecl_name
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
  (x,y) <- freshTVar (RecursiveUVar fv)
  tm <- withTerm mn PrdRep fv (TST.FreeVar loc PrdRep x fv) loc (TST.TypeScheme loc [] x) (genConstraints tm)
  addConstraint (SubType RecursionConstraint (TST.getTypeTerm tm) y)
  return tm
genConstraintsTermRecursive mn loc fv CnsRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  tm <- withTerm mn CnsRep fv (TST.FreeVar loc CnsRep y fv) loc (TST.TypeScheme loc [] y) (genConstraints tm)
  addConstraint (SubType RecursionConstraint x (TST.getTypeTerm tm))
  return tm
