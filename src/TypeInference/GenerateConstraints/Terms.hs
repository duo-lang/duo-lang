module TypeInference.GenerateConstraints.Terms
  ( genConstraintsTerm
  , genConstraintsTermRecursive
  , genConstraintsCommand
  , genConstraintsInstance
  ) where

import Control.Monad.Reader
import Data.Map qualified as M
import Data.Text qualified as T
import Pretty.Terms ()
import Pretty.Types ()
import Pretty.Constraints ()
import Pretty.Pretty ( ppPrint )
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Program qualified as TST
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Program qualified as Core
import Syntax.Common hiding (primOps)
import Syntax.Common.TypesPol
import TypeInference.GenerateConstraints.Definition
import TypeInference.Constraints
import Utils
import Lookup
import TypeInference.GenerateConstraints.Primitives (primOps)

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

genConstraintsCtxts :: LinearContext Pos -> LinearContext Neg -> ConstraintInfo -> GenM ()
genConstraintsCtxts ctx1 ctx2 info | length ctx1 /= length ctx2 = throwGenError ["genConstraintsCtxts: Linear contexts have unequal length"
                                                                                , "Constraint Info: " <> ppPrint info
                                                                                , "Pos context: " <> ppPrint ctx1
                                                                                , "Neg context: " <> ppPrint ctx2]
genConstraintsCtxts [] [] _ = return ()
genConstraintsCtxts ((PrdCnsType PrdRep ty1) : rest1) (PrdCnsType PrdRep ty2 : rest2) info = do
  addConstraint $ SubType info ty1 ty2
  genConstraintsCtxts rest1 rest2 info
genConstraintsCtxts ((PrdCnsType CnsRep ty1) : rest1) (PrdCnsType CnsRep ty2 : rest2) info = do
  addConstraint $ SubType info ty2 ty1
  genConstraintsCtxts rest1 rest2 info
genConstraintsCtxts (PrdCnsType PrdRep _:_) (PrdCnsType CnsRep _:_) info =
  throwGenError ["genConstraintsCtxts: Tried to constrain PrdType by CnsType", "Constraint Info: " <> ppPrint info]
genConstraintsCtxts (PrdCnsType CnsRep _:_) (PrdCnsType PrdRep _:_) info =
  throwGenError ["genConstraintsCtxts: Tried to constrain CnsType by PrdType", "ConstraintInfo: " <> ppPrint info]
genConstraintsCtxts [] (_:_) info =
  throwGenError ["genConstraintsCtxts: Linear contexts have unequal length.", "Constraint Info: " <> ppPrint info]
genConstraintsCtxts (_:_) [] info =
  throwGenError ["genConstraintsCtxts: Linear contexts have unequal length.", "Constraint Info: " <> ppPrint info]


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
  ty <- lookupContext rep idx
  return (TST.BoundVar loc rep ty idx)
--
-- Free variables:
--
-- Free variables can be looked up in the environment,
-- where they correspond to typing schemes. This typing
-- scheme has to be instantiated with fresh unification variables.
--
genConstraintsTerm (Core.FreeVar loc rep v) = do
  tys <- snd <$> lookupTerm rep v
  ty <- instantiateTypeScheme v loc tys
  return (TST.FreeVar loc rep ty v)
--
-- Structural Xtors:
--
genConstraintsTerm (Core.Xtor loc annot rep Structural xt subst) = do
  inferredSubst <- genConstraintsSubst subst
  let substTypes = TST.getTypArgs inferredSubst
  case rep of
    PrdRep -> return $ TST.Xtor loc annot rep (TyData   defaultLoc PosRep [MkXtorSig xt substTypes]) Structural xt inferredSubst
    CnsRep -> return $ TST.Xtor loc annot rep (TyCodata defaultLoc NegRep [MkXtorSig xt substTypes]) Structural xt inferredSubst
--
-- Nominal Xtors
--
genConstraintsTerm (Core.Xtor loc annot rep Nominal xt subst) = do
  -- First we infer the types of the arguments.
  substInferred <- genConstraintsSubst subst
  let substTypes = TST.getTypArgs substInferred
  -- Secondly we look up the argument types of the xtor in the type declaration.
  decl <- lookupDataDecl xt
  xtorSig <- lookupXtorSig xt NegRep
  -- Generate fresh unification variables for type parameters
  (args, tyParamsMap) <- freshTVarsForTypeParams (prdCnsToPol rep) decl
  -- Substitute these for the type parameters in the constructor signature
  let sig_args' = zonk tyParamsMap (sig_args xtorSig)
  -- Then we generate constraints between the inferred types of the substitution
  -- and the types we looked up, i.e. the types declared in the XtorSig.
  genConstraintsCtxts substTypes sig_args' (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
  case rep of
    PrdRep -> return (TST.Xtor loc annot rep (TyNominal defaultLoc PosRep Nothing (data_name decl) args) Nominal xt substInferred)
    CnsRep -> return (TST.Xtor loc annot rep (TyNominal defaultLoc NegRep Nothing (data_name decl) args) Nominal xt substInferred)
--
-- Refinement Xtors
--
genConstraintsTerm (Core.Xtor loc annot rep Refinement xt subst) = do
  -- First we infer the types of the arguments.
  substInferred <- genConstraintsSubst subst
  let substTypes = TST.getTypArgs substInferred
  -- Secondly we look up the argument types of the xtor in the type declaration.
  -- Since we infer refinement types, we have to look up the translated xtorSig.
  decl <- lookupDataDecl xt
  xtorSigUpper <- translateXtorSigUpper =<< lookupXtorSig xt NegRep
  -- Then we generate constraints between the inferred types of the substitution
  -- and the translations of the types we looked up, i.e. the types declared in the XtorSig.
  genConstraintsCtxts substTypes (sig_args xtorSigUpper) (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
  case rep of
    PrdRep -> return (TST.Xtor loc annot rep (TyDataRefined   defaultLoc PosRep (data_name decl) [MkXtorSig xt substTypes]) Refinement xt substInferred)
    CnsRep -> return (TST.Xtor loc annot rep (TyCodataRefined defaultLoc NegRep (data_name decl) [MkXtorSig xt substTypes]) Refinement xt substInferred)
--
-- Structural pattern and copattern matches:
--
genConstraintsTerm (Core.XCase loc annot rep Structural cases) = do
  inferredCases <- forM cases (\Core.MkCmdCase{ cmdcase_pat = Core.XtorPat loc xt args, cmdcase_loc, cmdcase_cmd} -> do
                      -- Generate positive and negative unification variables for all variables
                      -- bound in the pattern.
                      (uvarsPos, uvarsNeg) <- freshTVars args
                      -- Check the command in the context extended with the positive unification variables
                      cmdInferred <- withContext uvarsPos (genConstraintsCommand cmdcase_cmd)
                      -- Return the negative unification variables in the returned type.
                      return (TST.MkCmdCase cmdcase_loc (TST.XtorPat loc xt args) cmdInferred, MkXtorSig xt uvarsNeg))
  case rep of
    -- The return type is a structural type consisting of a XtorSig for each case.
    PrdRep -> return $ TST.XCase loc annot rep (TyCodata defaultLoc PosRep (snd <$> inferredCases)) Structural (fst <$> inferredCases)
    CnsRep -> return $ TST.XCase loc annot rep (TyData   defaultLoc NegRep (snd <$> inferredCases)) Structural (fst <$> inferredCases)
--
-- Nominal pattern and copattern matches
--
genConstraintsTerm (Core.XCase _ _ _ Nominal []) =
  -- We know that empty matches cannot be parsed as nominal.
  -- It is therefore safe to pattern match on the head of the xtors in the other cases.
  throwGenError ["Unreachable: A nominal match needs to have at least one case."]
genConstraintsTerm (Core.XCase loc annot rep Nominal cases@(pmcase:_)) = do
  -- We lookup the data declaration based on the first pattern match case.
  decl <- lookupDataDecl (case Core.cmdcase_pat pmcase of (Core.XtorPat _ xt _) -> xt)
  -- We check that all cases in the pattern match belong to the type declaration.
  checkCorrectness ((\cs -> case Core.cmdcase_pat cs of Core.XtorPat _ xt _ -> xt) <$> cases) decl
  -- We check that all xtors in the type declaration are matched against.
  checkExhaustiveness ((\cs -> case Core.cmdcase_pat cs of Core.XtorPat _ xt _ -> xt) <$> cases) decl
  -- Generate fresh unification variables for type parameters
  (args, tyParamsMap) <- freshTVarsForTypeParams (prdCnsToPol rep) decl

  inferredCases <- forM cases (\Core.MkCmdCase {cmdcase_loc, cmdcase_pat = Core.XtorPat loc' xt args, cmdcase_cmd} -> do
                   -- We lookup the types belonging to the xtor in the type declaration.
                   posTypes <- sig_args <$> lookupXtorSig xt PosRep
                   negTypes <- sig_args <$> lookupXtorSig xt NegRep
                   -- Substitute fresh unification variables for type parameters
                   let posTypes' = zonk tyParamsMap posTypes
                   let negTypes' = zonk tyParamsMap negTypes
                   -- We generate constraints for the command in the context extended
                   -- with the types from the signature.
                   cmdInferred <- withContext posTypes' (genConstraintsCommand cmdcase_cmd)
                   return (TST.MkCmdCase cmdcase_loc (TST.XtorPat loc' xt args) cmdInferred, MkXtorSig xt negTypes'))
  case rep of
    PrdRep -> return $ TST.XCase loc annot rep (TyNominal defaultLoc PosRep Nothing (data_name decl) args) Nominal (fst <$> inferredCases)
    CnsRep -> return $ TST.XCase loc annot rep (TyNominal defaultLoc NegRep Nothing (data_name decl) args) Nominal (fst <$> inferredCases)
--
-- Refinement pattern and copattern matches
--
genConstraintsTerm (Core.XCase _ _ _ Refinement []) =
  -- We know that empty matches cannot be parsed as Refinement.
  -- It is therefore safe to pattern match on the head of the xtors in the other cases.
  throwGenError ["Unreachable: A refinement match needs to have at least one case."]
genConstraintsTerm (Core.XCase loc annot rep Refinement cases@(pmcase:_)) = do
  -- We lookup the data declaration based on the first pattern match case.
  decl <- lookupDataDecl (case Core.cmdcase_pat pmcase of (Core.XtorPat _ xt _) -> xt)
  -- We check that all cases in the pattern match belong to the type declaration.
  checkCorrectness ((\cs -> case Core.cmdcase_pat cs of Core.XtorPat _ xt _ -> xt) <$> cases) decl
  inferredCases <- forM cases (\Core.MkCmdCase {cmdcase_loc, cmdcase_pat = Core.XtorPat loc xt args , cmdcase_cmd} -> do
                       -- Generate positive and negative unification variables for all variables
                       -- bound in the pattern.
                       (uvarsPos, uvarsNeg) <- freshTVars args
                       -- Check the command in the context extended with the positive unification variables
                       cmdInferred <- withContext uvarsPos (genConstraintsCommand cmdcase_cmd)
                       -- We have to bound the unification variables with the lower and upper bounds generated
                       -- from the information in the type declaration. These lower and upper bounds correspond
                       -- to the least and greatest type translation.
                       lowerBound <- sig_args <$> (translateXtorSigLower =<< lookupXtorSig xt PosRep)
                       upperBound <- sig_args <$> (translateXtorSigUpper =<< lookupXtorSig xt NegRep)
                       genConstraintsCtxts lowerBound uvarsNeg (PatternMatchConstraint loc)
                       genConstraintsCtxts uvarsPos upperBound (PatternMatchConstraint loc)
                       -- For the type, we return the unification variables which are now bounded by the least
                       -- and greatest type translation.
                       return (TST.MkCmdCase cmdcase_loc (TST.XtorPat loc xt args) cmdInferred, MkXtorSig xt uvarsNeg))
  case rep of
    PrdRep -> return $ TST.XCase loc annot rep (TyCodataRefined defaultLoc PosRep (data_name decl) (snd <$> inferredCases)) Refinement (fst <$> inferredCases)
    CnsRep -> return $ TST.XCase loc annot rep (TyDataRefined   defaultLoc NegRep (data_name decl) (snd <$> inferredCases)) Refinement (fst <$> inferredCases)
--
-- Mu and TildeMu abstractions:
--
genConstraintsTerm (Core.MuAbs loc annot PrdRep bs cmd) = do
  (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
  cmdInferred <- withContext [PrdCnsType CnsRep uvneg] (genConstraintsCommand cmd)
  return (TST.MuAbs loc annot PrdRep uvpos bs cmdInferred)
genConstraintsTerm (Core.MuAbs loc annot CnsRep bs cmd) = do
  (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
  cmdInferred <- withContext [PrdCnsType PrdRep uvpos] (genConstraintsCommand cmd)
  return (TST.MuAbs loc annot CnsRep uvneg bs cmdInferred)
genConstraintsTerm (Core.PrimLitI64 loc i) = pure $ TST.PrimLitI64 loc i
genConstraintsTerm (Core.PrimLitF64 loc d) = pure $ TST.PrimLitF64 loc d

genConstraintsCommand :: Core.Command -> GenM TST.Command
genConstraintsCommand (Core.ExitSuccess loc) =
  return (TST.ExitSuccess loc)
genConstraintsCommand (Core.ExitFailure loc) =
  return (TST.ExitFailure loc)
genConstraintsCommand (Core.Jump loc fv) = do
  -- Ensure that the referenced command is in scope
  _ <- lookupCommand fv
  return (TST.Jump loc fv)
genConstraintsCommand (Core.Print loc prd cmd) = do
  prd' <- genConstraintsTerm prd
  cmd' <- genConstraintsCommand cmd
  return (TST.Print loc prd' cmd')
genConstraintsCommand (Core.Read loc cns) = do
  cns' <- genConstraintsTerm cns
  addConstraint (SubType (ReadConstraint loc)  (TyNominal defaultLoc PosRep Nothing peanoNm []) (TST.getTypeTerm cns'))
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
    Nothing -> throwGenError [T.pack $ "Unreachable: Signature for primitive op " ++ primOpKeyword op ++ primTypeKeyword pt ++ " not defined"]
    Just sig -> do
      _ <- genConstraintsCtxts substTypes sig (PrimOpArgsConstraint loc)
      return (TST.PrimOp loc pt op substInferred)

genConstraintsInstance :: Core.InstanceDeclaration -> GenM TST.InstanceDeclaration
genConstraintsInstance Core.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases } = do
  -- We lookup the class and type definition of the method.
  decl <- lookupClassDecl instancedecl_name
  -- We check that all implementations belong to the same type class.
  checkInstance (fst <$> decl) ((\(Core.XtorPat _ xt _) -> MkMethodName $ unXtorName xt) . Core.instancecase_pat <$> instancedecl_cases) 
  -- Generate fresh unification variables for type parameters
  freshTVars <- sequence $ freshTVars . (\(Core.XtorPat _ _ tvars) -> tvars) . Core.instancecase_pat <$> instancedecl_cases

  inferredCases <- forM instancedecl_cases (\Core.MkInstanceCase { instancecase_loc, instancecase_pat, instancecase_cmd } -> do
                   cmdInferred <- genConstraintsCommand instancecase_cmd
                   pure TST.MkInstanceCase { instancecase_loc = instancecase_loc
                                           , instancecase_pat = instancecase_pat
                                           , instancecase_cmd = cmdInferred
                                           })
  pure TST.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                                 , instancedecl_doc = instancedecl_doc
                                 , instancedecl_name = instancedecl_name
                                 , instancedecl_typ = instancedecl_typ
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
  tm <- withTerm mn PrdRep fv (TST.FreeVar loc PrdRep x fv) loc (TypeScheme loc [] x) (genConstraintsTerm tm)
  addConstraint (SubType RecursionConstraint (TST.getTypeTerm tm) y)
  return tm
genConstraintsTermRecursive mn loc fv CnsRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  tm <- withTerm mn CnsRep fv (TST.FreeVar loc CnsRep y fv) loc (TypeScheme loc [] y) (genConstraintsTerm tm)
  addConstraint (SubType RecursionConstraint x (TST.getTypeTerm tm))
  return tm
