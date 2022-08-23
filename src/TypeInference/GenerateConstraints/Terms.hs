module TypeInference.GenerateConstraints.Terms
  ( genConstraintsTerm
  , genConstraintsTermRecursive
  , genConstraintsCommand
  , genConstraintsInstance
  ) where

import Control.Monad.Reader
import Data.Map qualified as M
import Errors
import Syntax.CST.Terms qualified as CST
import Syntax.RST.Program qualified as RST
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Program qualified as TST
import Syntax.TST.Types qualified as TST
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Program qualified as Core
import Syntax.RST.Types qualified as RST
import Syntax.Common.PrdCns
import Syntax.Common.Names
import Syntax.Common.Polarity
import TypeInference.GenerateConstraints.Definition
import TypeInference.Constraints
import Utils
import Lookup
import TypeInference.GenerateConstraints.Primitives (primOps)
import Syntax.RST.Program (ClassDeclaration(classdecl_kinds))
import Translate.Embed

---------------------------------------------------------------------------------------------
-- Substitutions and Linear Contexts
---------------------------------------------------------------------------------------------

genConstraintsPCTerm :: Core.PrdCnsTerm
                     -> GenM TST.PrdCnsTerm
genConstraintsPCTerm (Core.PrdTerm tm) = TST.PrdTerm <$> genConstraintsTerm tm
genConstraintsPCTerm (Core.CnsTerm tm) = TST.CnsTerm <$> genConstraintsTerm tm

genConstraintsSubst :: Core.Substitution
                    -> GenM TST.Substitution
genConstraintsSubst subst = sequence (genConstraintsPCTerm <$> subst)

genConstraintsCtxts :: RST.LinearContext Pos -> RST.LinearContext Neg -> ConstraintInfo -> GenM ()
genConstraintsCtxts ctx1 ctx2 info | length ctx1 /= length ctx2 = do
  loc <- asks (location . snd)
  throwGenError (LinearContextsUnequalLength loc info ctx1 ctx2)
genConstraintsCtxts [] [] _ = return ()
genConstraintsCtxts ((RST.PrdCnsType PrdRep ty1) : rest1) (RST.PrdCnsType PrdRep ty2 : rest2) info = do
  addConstraint $ SubType info (unEmbedType ty1) (unEmbedType ty2)
  genConstraintsCtxts rest1 rest2 info
genConstraintsCtxts ((RST.PrdCnsType CnsRep ty1) : rest1) (RST.PrdCnsType CnsRep ty2 : rest2) info = do
  addConstraint $ SubType info (unEmbedType ty2) (unEmbedType ty1)
  genConstraintsCtxts rest1 rest2 info
genConstraintsCtxts (RST.PrdCnsType PrdRep _:_) (RST.PrdCnsType CnsRep _:_) info = do
  loc <- asks (location . snd)
  throwGenError (LinearContextIncompatibleTypeMode loc Prd info)
genConstraintsCtxts (RST.PrdCnsType CnsRep _:_) (RST.PrdCnsType PrdRep _:_) info = do
  loc <- asks (location . snd)
  throwGenError (LinearContextIncompatibleTypeMode loc Cns info)
genConstraintsCtxts ctx1@[] ctx2@(_:_) info = do
  loc <- asks (location . snd)
  throwGenError (LinearContextsUnequalLength loc info ctx1 ctx2)
genConstraintsCtxts ctx1@(_:_) ctx2@[] info = do
  loc <- asks (location . snd)
  throwGenError (LinearContextsUnequalLength loc info ctx1 ctx2)


genConstraintsCtxtsTST :: TST.LinearContext Pos -> TST.LinearContext Neg -> ConstraintInfo -> GenM ()
genConstraintsCtxtsTST ctx1 ctx2 info | length ctx1 /= length ctx2 = do
  loc <- asks (location . snd)
  throwGenError (LinearContextsUnequalLength loc info (embedTSTLinearContext ctx1) (embedTSTLinearContext ctx2))
genConstraintsCtxtsTST [] [] _ = return ()
genConstraintsCtxtsTST ((TST.PrdCnsType PrdRep ty1) : rest1) (TST.PrdCnsType PrdRep ty2 : rest2) info = do
  addConstraint $ SubType info ty1 ty2
  genConstraintsCtxtsTST rest1 rest2 info
genConstraintsCtxtsTST ((TST.PrdCnsType CnsRep ty1) : rest1) (TST.PrdCnsType CnsRep ty2 : rest2) info = do
  addConstraint $ SubType info ty2 ty1
  genConstraintsCtxtsTST rest1 rest2 info
genConstraintsCtxtsTST (TST.PrdCnsType PrdRep _:_) (TST.PrdCnsType CnsRep _:_) info = do
  loc <- asks (location . snd)
  throwGenError (LinearContextIncompatibleTypeMode loc Prd info)
genConstraintsCtxtsTST (TST.PrdCnsType CnsRep _:_) (TST.PrdCnsType PrdRep _:_) info = do
  loc <- asks (location . snd)
  throwGenError (LinearContextIncompatibleTypeMode loc Cns info)
genConstraintsCtxtsTST ctx1@[] ctx2@(_:_) info = do
  loc <- asks (location . snd)
  throwGenError (LinearContextsUnequalLength loc info (embedTSTLinearContext ctx1) (embedTSTLinearContext ctx2))
genConstraintsCtxtsTST ctx1@(_:_) ctx2@[] info = do
  loc <- asks (location . snd)
  throwGenError (LinearContextsUnequalLength loc info (embedTSTLinearContext ctx1) (embedTSTLinearContext ctx2))

---------------------------------------------------------------------------------------------
-- Kinds
---------------------------------------------------------------------------------------------

checkVariantType :: RST.VariantType pol -> TST.VariantType pol 
checkVariantType (RST.CovariantType ty) = TST.CovariantType (checkKind ty)
checkVariantType (RST.ContravariantType ty) = TST.ContravariantType (checkKind ty)

checkPrdCnsType :: RST.PrdCnsType pol -> TST.PrdCnsType pol
checkPrdCnsType (RST.PrdCnsType rep ty) = TST.PrdCnsType rep (checkKind ty)

checkLinearContext :: RST.LinearContext pol -> TST.LinearContext pol
checkLinearContext = map checkPrdCnsType

checkXtorSig :: RST.XtorSig pol -> TST.XtorSig pol
checkXtorSig RST.MkXtorSig { sig_name = nm, sig_args = ctxt } = TST.MkXtorSig {sig_name = nm, sig_args = checkLinearContext ctxt }

checkKind :: RST.Typ pol -> TST.Typ pol 
checkKind (RST.TySkolemVar loc pol mk tv) = TST.TySkolemVar loc pol mk tv
checkKind (RST.TyUniVar loc pol mk tv) = TST.TyUniVar loc pol mk tv
checkKind (RST.TyRecVar loc pol mk rv) = TST.TyRecVar loc pol mk rv
checkKind (RST.TyData loc pol xtors) = TST.TyData loc pol (map checkXtorSig xtors)
checkKind (RST.TyCodata loc pol xtors) = TST.TyCodata loc pol (map checkXtorSig xtors)
checkKind (RST.TyDataRefined loc pol tn xtors) = TST.TyDataRefined loc pol tn (map checkXtorSig xtors)
checkKind (RST.TyCodataRefined loc pol tn xtors) = TST.TyCodataRefined loc pol tn (map checkXtorSig xtors)
checkKind (RST.TyNominal loc pol mk tn vart) = TST.TyNominal loc pol mk tn (map checkVariantType vart)
checkKind (RST.TySyn loc pol tn ty) = TST.TySyn loc pol tn (checkKind ty)
checkKind (RST.TyBot loc mk) = TST.TyBot loc mk
checkKind (RST.TyTop loc mk) = TST.TyTop loc mk
checkKind (RST.TyUnion loc mk ty1 ty2) = TST.TyUnion loc mk (checkKind ty1) (checkKind ty2)
checkKind (RST.TyInter loc mk ty1 ty2) = TST.TyInter loc mk (checkKind ty1) (checkKind ty2)
checkKind (RST.TyRec loc pol rv ty) = TST.TyRec loc pol rv (checkKind ty)
checkKind (RST.TyI64 loc pol) = TST.TyI64 loc pol
checkKind (RST.TyF64 loc pol) = TST.TyF64 loc pol
checkKind (RST.TyChar loc pol) = TST.TyChar loc pol
checkKind (RST.TyString loc pol) = TST.TyString loc pol
checkKind (RST.TyFlipPol pol ty) = TST.TyFlipPol pol (checkKind ty)


---------------------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------------------

-- | Generate the constraints for a given Term.
genConstraintsTerm :: Core.Term pc
                    -> GenM (TST.Term pc)
--
-- Bound variables:
--
-- Bound variables can be looked up in the context.
--
genConstraintsTerm (Core.BoundVar loc rep idx) = do
  ty <- lookupContext loc rep idx
  return (TST.BoundVar loc rep ty idx)
--
-- Free variables:
--
-- Free variables can be looked up in the environment,
-- where they correspond to typing schemes. This typing
-- scheme has to be instantiated with fresh unification variables.
--
genConstraintsTerm (Core.FreeVar loc rep v) = do
  tys <- snd <$> lookupTerm loc rep v
  ty <- instantiateTypeScheme v loc tys
  return (TST.FreeVar loc rep ty v)
--
-- Structural Xtors:
--
genConstraintsTerm (Core.Xtor loc annot rep CST.Structural xt subst) = do
  inferredSubst <- genConstraintsSubst subst
  let substTypes = TST.getTypArgs inferredSubst
  case rep of
    PrdRep -> return $ TST.Xtor loc annot rep (TST.TyData   defaultLoc PosRep [TST.MkXtorSig xt substTypes]) CST.Structural xt inferredSubst
    CnsRep -> return $ TST.Xtor loc annot rep (TST.TyCodata defaultLoc NegRep [TST.MkXtorSig xt substTypes]) CST.Structural xt inferredSubst
--
-- Nominal Xtors
--
genConstraintsTerm (Core.Xtor loc annot rep CST.Nominal xt subst) = do
  -- First we infer the types of the arguments.
  substInferred <- genConstraintsSubst subst
  let substTypes = TST.getTypArgs substInferred
  -- Secondly we look up the argument types of the xtor in the type declaration.
  decl <- lookupDataDecl loc xt
  xtorSig <- lookupXtorSig loc xt NegRep
  -- Generate fresh unification variables for type parameters
  (args, tyParamsMap) <- freshTVarsForTypeParams (prdCnsToPol rep) decl
  -- Substitute these for the type parameters in the constructor signature
  let sig_args' = TST.zonk TST.SkolemRep tyParamsMap (unEmbedLinearContext (RST.sig_args xtorSig))
  -- Then we generate constraints between the inferred types of the substitution
  -- and the types we looked up, i.e. the types declared in the XtorSig.
  genConstraintsCtxtsTST substTypes sig_args' (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
  case rep of
    PrdRep -> return (TST.Xtor loc annot rep (TST.TyNominal defaultLoc PosRep Nothing (RST.data_name decl) args) CST.Nominal xt substInferred)
    CnsRep -> return (TST.Xtor loc annot rep (TST.TyNominal defaultLoc NegRep Nothing (RST.data_name decl) args) CST.Nominal xt substInferred)
--
-- Refinement Xtors
--
genConstraintsTerm (Core.Xtor loc annot rep CST.Refinement xt subst) = do
  -- First we infer the types of the arguments.
  substInferred <- genConstraintsSubst subst
  let substTypes = TST.getTypArgs substInferred
  -- Secondly we look up the argument types of the xtor in the type declaration.
  -- Since we infer refinement types, we have to look up the translated xtorSig.
  decl <- lookupDataDecl loc xt
  xtorSigUpper <- translateXtorSigUpper =<< lookupXtorSig loc xt NegRep
  -- Then we generate constraints between the inferred types of the substitution
  -- and the translations of the types we looked up, i.e. the types declared in the XtorSig.
  genConstraintsCtxts (map embedTSTPrdCnsType substTypes) (RST.sig_args (embedTSTXtorSig xtorSigUpper)) (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
  case rep of
    PrdRep -> return (TST.Xtor loc annot rep (TST.TyDataRefined   defaultLoc PosRep (RST.data_name decl) [TST.MkXtorSig xt substTypes]) CST.Refinement xt substInferred)
    CnsRep -> return (TST.Xtor loc annot rep (TST.TyCodataRefined defaultLoc NegRep (RST.data_name decl) [TST.MkXtorSig xt substTypes]) CST.Refinement xt substInferred)
--
-- Structural pattern and copattern matches:
--
genConstraintsTerm (Core.XCase loc annot rep CST.Structural cases) = do
  inferredCases <- forM cases (\Core.MkCmdCase{ cmdcase_pat = Core.XtorPat loc xt args, cmdcase_loc, cmdcase_cmd} -> do
                      -- Generate positive and negative unification variables for all variables
                      -- bound in the pattern.
                      (uvarsPos, uvarsNeg) <- freshTVars args
                      -- Check the command in the context extended with the positive unification variables
                      cmdInferred <- withContextTST uvarsPos (genConstraintsCommand cmdcase_cmd)
                      -- Return the negative unification variables in the returned type.
                      return (TST.MkCmdCase cmdcase_loc (TST.XtorPat loc xt args) cmdInferred, TST.MkXtorSig xt uvarsNeg))
  case rep of
    -- The return type is a structural type consisting of a XtorSig for each case.
    PrdRep -> return $ TST.XCase loc annot rep (TST.TyCodata defaultLoc PosRep (snd <$> inferredCases)) CST.Structural (fst <$> inferredCases)
    CnsRep -> return $ TST.XCase loc annot rep (TST.TyData   defaultLoc NegRep (snd <$> inferredCases)) CST.Structural (fst <$> inferredCases)
--
-- Nominal pattern and copattern matches
--
genConstraintsTerm (Core.XCase loc _ _ CST.Nominal []) =
  -- We know that empty matches cannot be parsed as nominal.
  -- It is therefore safe to pattern match on the head of the xtors in the other cases.
  throwGenError (EmptyNominalMatch loc)
genConstraintsTerm (Core.XCase loc annot rep CST.Nominal cases@(pmcase:_)) = do
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
                   posTypes <- RST.sig_args <$> lookupXtorSig loc xt PosRep
                   negTypes <- RST.sig_args <$> lookupXtorSig loc xt NegRep
                   -- Substitute fresh unification variables for type parameters
                   let posTypes' = TST.zonk TST.SkolemRep tyParamsMap (unEmbedLinearContext posTypes)
                   let negTypes' = TST.zonk TST.SkolemRep tyParamsMap (unEmbedLinearContext negTypes)
                   -- We generate constraints for the command in the context extended
                   -- with the types from the signature.
                   cmdInferred <- withContextTST posTypes' (genConstraintsCommand cmdcase_cmd)
                   return (TST.MkCmdCase cmdcase_loc (TST.XtorPat loc' xt args) cmdInferred, TST.MkXtorSig xt negTypes'))
  case rep of
    PrdRep -> return $ TST.XCase loc annot rep (TST.TyNominal defaultLoc PosRep Nothing (RST.data_name decl) args) CST.Nominal (fst <$> inferredCases)
    CnsRep -> return $ TST.XCase loc annot rep (TST.TyNominal defaultLoc NegRep Nothing (RST.data_name decl) args) CST.Nominal (fst <$> inferredCases)
--
-- Refinement pattern and copattern matches
--
genConstraintsTerm (Core.XCase loc _ _ CST.Refinement []) =
  -- We know that empty matches cannot be parsed as Refinement.
  -- It is therefore safe to pattern match on the head of the xtors in the other cases.
  throwGenError (EmptyRefinementMatch loc)
genConstraintsTerm (Core.XCase loc annot rep CST.Refinement cases@(pmcase:_)) = do
  -- We lookup the data declaration based on the first pattern match case.
  decl <- lookupDataDecl loc (case Core.cmdcase_pat pmcase of (Core.XtorPat _ xt _) -> xt)
  -- We check that all cases in the pattern match belong to the type declaration.
  checkCorrectness loc ((\cs -> case Core.cmdcase_pat cs of Core.XtorPat _ xt _ -> xt) <$> cases) decl
  inferredCases <- forM cases (\Core.MkCmdCase {cmdcase_loc, cmdcase_pat = Core.XtorPat loc xt args , cmdcase_cmd} -> do
                       -- Generate positive and negative unification variables for all variables
                       -- bound in the pattern.
                       (uvarsPos, uvarsNeg) <- freshTVars args
                       -- Check the command in the context extended with the positive unification variables
                       cmdInferred <- withContextTST uvarsPos (genConstraintsCommand cmdcase_cmd)
                       -- We have to bound the unification variables with the lower and upper bounds generated
                       -- from the information in the type declaration. These lower and upper bounds correspond
                       -- to the least and greatest type translation.
                       lowerBound <- TST.sig_args <$> (translateXtorSigLower =<< lookupXtorSig loc xt PosRep)
                       upperBound <- TST.sig_args <$> (translateXtorSigUpper =<< lookupXtorSig loc xt NegRep)
                       genConstraintsCtxtsTST lowerBound uvarsNeg (PatternMatchConstraint loc)
                       genConstraintsCtxtsTST uvarsPos upperBound (PatternMatchConstraint loc)
                       -- For the type, we return the unification variables which are now bounded by the least
                       -- and greatest type translation.
                       return (TST.MkCmdCase cmdcase_loc (TST.XtorPat loc xt args) cmdInferred, TST.MkXtorSig xt uvarsNeg))
  case rep of
    PrdRep -> return $ TST.XCase loc annot rep (TST.TyCodataRefined defaultLoc PosRep (RST.data_name decl) (snd <$> inferredCases)) CST.Refinement (fst <$> inferredCases)
    CnsRep -> return $ TST.XCase loc annot rep (TST.TyDataRefined   defaultLoc NegRep (RST.data_name decl) (snd <$> inferredCases)) CST.Refinement (fst <$> inferredCases)
--
-- Mu and TildeMu abstractions:
--
genConstraintsTerm (Core.MuAbs loc annot PrdRep bs cmd) = do
  (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
  cmdInferred <- withContextTST [TST.PrdCnsType CnsRep uvneg] (genConstraintsCommand cmd)
  return (TST.MuAbs loc annot PrdRep uvpos bs cmdInferred)
genConstraintsTerm (Core.MuAbs loc annot CnsRep bs cmd) = do
  (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
  cmdInferred <- withContextTST [TST.PrdCnsType PrdRep uvpos] (genConstraintsCommand cmd)
  return (TST.MuAbs loc annot CnsRep uvneg bs cmdInferred)
genConstraintsTerm (Core.PrimLitI64 loc i) = pure $ TST.PrimLitI64 loc i
genConstraintsTerm (Core.PrimLitF64 loc d) = pure $ TST.PrimLitF64 loc d
genConstraintsTerm (Core.PrimLitChar loc d) = pure $ TST.PrimLitChar loc d
genConstraintsTerm (Core.PrimLitString loc d) = pure $ TST.PrimLitString loc d

genConstraintsCommand :: Core.Command -> GenM TST.Command
genConstraintsCommand (Core.ExitSuccess loc) =
  return (TST.ExitSuccess loc)
genConstraintsCommand (Core.ExitFailure loc) =
  return (TST.ExitFailure loc)
genConstraintsCommand (Core.Jump loc fv) = do
  -- Ensure that the referenced command is in scope
  _ <- lookupCommand loc fv
  return (TST.Jump loc fv)
genConstraintsCommand (Core.Method loc mn cn subst) = do
  decl <- lookupClassDecl loc cn
    -- fresh type var and subsitution for type class variable(s)
  tyParamsMap <- createMethodSubst loc decl
  negTypes <- lookupMethodType loc mn decl NegRep
  let negTypes' = TST.zonk TST.SkolemRep tyParamsMap (unEmbedLinearContext negTypes)
  -- infer arg types
  substInferred <- genConstraintsSubst subst
  let substTypes = TST.getTypArgs substInferred
  genConstraintsCtxtsTST substTypes negTypes' (TypeClassConstraint loc)
  return (TST.Method loc mn cn substInferred)
genConstraintsCommand (Core.Print loc prd cmd) = do
  prd' <- genConstraintsTerm prd
  cmd' <- genConstraintsCommand cmd
  return (TST.Print loc prd' cmd')
genConstraintsCommand (Core.Read loc cns) = do
  cns' <- genConstraintsTerm cns
  addConstraint (SubType (ReadConstraint loc)  (TST.TyNominal defaultLoc PosRep Nothing peanoNm []) (TST.getTypeTerm cns'))
  return (TST.Read loc cns')
genConstraintsCommand (Core.Apply loc annot t1 t2) = do
  t1' <- genConstraintsTerm t1
  t2' <- genConstraintsTerm t2
  addConstraint (SubType (CommandConstraint loc) (TST.getTypeTerm t1') (TST.getTypeTerm t2'))
  return (TST.Apply loc annot Nothing t1' t2')
genConstraintsCommand (Core.PrimOp loc pt op subst) = do
  substInferred <- genConstraintsSubst subst
  let substTypes = TST.getTypArgs substInferred
  case M.lookup (pt, op) primOps of
    Nothing -> throwGenError (PrimitiveOpMissingSignature loc op pt)
    Just sig -> do
      _ <- genConstraintsCtxtsTST substTypes (unEmbedLinearContext sig) (PrimOpArgsConstraint loc)
      return (TST.PrimOp loc pt op substInferred)

genConstraintsInstance :: Core.InstanceDeclaration -> GenM TST.InstanceDeclaration
genConstraintsInstance Core.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases } = do
  -- We lookup the class declaration  of the instance.
  decl <- lookupClassDecl instancedecl_loc instancedecl_name
  -- We check that all implementations belong to the same type class.
  checkInstanceCoverage instancedecl_loc decl ((\(Core.XtorPat _ xt _) -> MkMethodName $ unXtorName xt) . Core.instancecase_pat <$> instancedecl_cases) 
  -- Generate fresh unification variables for type parameters
  let instancetyp = (unEmbedType.fst $ instancedecl_typ, unEmbedType.snd $ instancedecl_typ)
  let tyParamsMap = paramsMap (classdecl_kinds decl) [instancetyp]
  inferredCases <- forM instancedecl_cases (\Core.MkInstanceCase { instancecase_loc, instancecase_pat = Core.XtorPat loc xt args, instancecase_cmd } -> do
                   let mn :: MethodName = MkMethodName $ unXtorName xt
                   -- We lookup the types belonging to the xtor in the type declaration.
                   posTypes <- lookupMethodType instancecase_loc mn decl PosRep
                   negTypes <- lookupMethodType instancecase_loc mn decl NegRep
                   -- Substitute fresh unification variables for type parameters
                   let posTypes' = TST.zonk TST.SkolemRep tyParamsMap (unEmbedLinearContext posTypes)
                   let negTypes' = TST.zonk TST.SkolemRep tyParamsMap (unEmbedLinearContext negTypes)
                   -- We generate constraints for the command in the context extended
                   -- with the types from the signature.
                   cmdInferred <- withContextTST posTypes' (genConstraintsCommand instancecase_cmd)
                   genConstraintsCtxtsTST posTypes' negTypes' (InstanceConstraint instancecase_loc)
                   pure TST.MkInstanceCase { instancecase_loc = instancecase_loc
                                           , instancecase_pat = Core.XtorPat loc xt args
                                           , instancecase_cmd = cmdInferred
                                           })
  pure TST.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                                 , instancedecl_doc = instancedecl_doc
                                 , instancedecl_name = instancedecl_name
                                 , instancedecl_typ = (unEmbedType.fst $ instancedecl_typ, unEmbedType.snd $ instancedecl_typ)
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
  tm <- withTerm mn PrdRep fv (TST.FreeVar loc PrdRep x fv) loc (TST.TypeScheme loc [] x) (genConstraintsTerm tm)
  addConstraint (SubType RecursionConstraint (TST.getTypeTerm tm) y)
  return tm
genConstraintsTermRecursive mn loc fv CnsRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  tm <- withTerm mn CnsRep fv (TST.FreeVar loc CnsRep y fv) loc (TST.TypeScheme loc [] y) (genConstraintsTerm tm)
  addConstraint (SubType RecursionConstraint x (TST.getTypeTerm tm))
  return tm
