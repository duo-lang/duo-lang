module TypeInference.GenerateConstraints.Terms
  ( genConstraintsTerm
  , genConstraintsTermRecursive
  , genConstraintsCommand
  ) where

import Control.Monad.Reader
import Pretty.Terms ()
import Pretty.Types ()
import Pretty.Constraints ()
import Pretty.Pretty ( ppPrint )
import Syntax.AST.Terms
import Syntax.CommonTerm
import Syntax.AST.Types
import TypeInference.GenerateConstraints.Definition
import TypeInference.Constraints
import Utils
import Lookup

---------------------------------------------------------------------------------------------
-- Substitutions and Linear Contexts
---------------------------------------------------------------------------------------------

genConstraintsPCTerm :: PrdCnsTerm Parsed
                     -> GenM (PrdCnsTerm Inferred)
genConstraintsPCTerm (PrdTerm tm) = PrdTerm <$> genConstraintsTerm tm
genConstraintsPCTerm (CnsTerm tm) = CnsTerm <$> genConstraintsTerm tm

genConstraintsSubst :: Substitution Parsed
                   -> GenM (Substitution Inferred)
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


splitContext :: Int -- ^ The offset of the projected type
             -> PrdCnsRep pc -- ^ The expected mode of the type
             -> LinearContext pol -- ^ The context to be split
             -> (LinearContext pol, Typ (PrdCnsFlip pc pol), LinearContext pol)
splitContext n PrdRep sig = case splitAt n sig of 
                              (_, []) -> error "splitContext: Too short."
                              (_, PrdCnsType CnsRep _:_) -> error "splitContext: Found CnsType, expected PrdType."
                              (tys1, PrdCnsType PrdRep ty:tys2) -> (tys1, ty, tys2)
splitContext n CnsRep sig = case splitAt n sig of
                              (_, []) -> error "splitContext: Too short."
                              (_, PrdCnsType PrdRep _:_) -> error "splitContext: Found PrdType, expected CnsType."
                              (tys1, PrdCnsType CnsRep ty:tys2) -> (tys1, ty, tys2)

---------------------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------------------

-- | Generate the constraints for a given Term.
genConstraintsTerm :: Term pc Parsed
                    -> GenM (Term pc Inferred)
--
-- Bound variables:
--
-- Bound variables can be looked up in the context.
--
genConstraintsTerm (BoundVar loc rep idx) = do
  ty <- lookupContext rep idx
  return (BoundVar (loc, ty) rep idx)
--
-- Free variables:
--
-- Free variables can be looked up in the environment,
-- where they correspond to typing schemes. This typing
-- scheme has to be instantiated with fresh unification variables.
--
genConstraintsTerm (FreeVar loc rep v) = do
  tys <- snd <$> lookupTerm rep v
  ty <- instantiateTypeScheme v loc tys
  return (FreeVar (loc, ty) rep v)
--
-- Structural Xtors:
--
genConstraintsTerm (Xtor loc rep xt@MkXtorName { xtorNominalStructural = Structural } subst) = do
  inferredSubst <- genConstraintsSubst subst
  let substTypes = getTypArgs inferredSubst
  case rep of
    PrdRep -> return $ Xtor (loc, TyData   PosRep Nothing [MkXtorSig xt substTypes]) rep xt inferredSubst
    CnsRep -> return $ Xtor (loc, TyCodata NegRep Nothing [MkXtorSig xt substTypes]) rep xt inferredSubst
--
-- Nominal Xtors:
--
genConstraintsTerm (Xtor loc rep xt@MkXtorName { xtorNominalStructural = Nominal } subst) = do
  -- First we infer the types of the arguments.
  substInferred <- genConstraintsSubst subst
  let substTypes = getTypArgs substInferred
  -- Secondly we look up the argument types of the xtor in the type declaration.
  decl <- lookupDataDecl xt
  xtorSig <- lookupXtorSig xt NegRep
  -- Then we generate constraints between the inferred types of the substitution
  -- and the types we looked up, i.e. the types declared in the XtorSig.
  genConstraintsCtxts substTypes (sig_args xtorSig) (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
  case rep of
    PrdRep -> return (Xtor (loc, TyNominal PosRep Nothing (data_name decl)) rep xt substInferred)
    CnsRep -> return (Xtor (loc, TyNominal NegRep Nothing (data_name decl)) rep xt substInferred)
--
-- Refinement Xtors:
--
genConstraintsTerm (Xtor loc rep xt@MkXtorName { xtorNominalStructural = Refinement } subst) = do
  -- First we infer the types of the arguments.
  substInferred <- genConstraintsSubst subst
  let substTypes = getTypArgs substInferred
  -- Secondly we look up the argument types of the xtor in the type declaration.
  -- Since we infer refinement types, we have to look up the translated xtorSig.
  decl <- lookupDataDecl xt
  xtorSigUpper <- translateXtorSigUpper =<< lookupXtorSig xt NegRep
  -- Then we generate constraints between the inferred types of the substitution
  -- and the translations of the types we looked up, i.e. the types declared in the XtorSig.
  genConstraintsCtxts substTypes (sig_args xtorSigUpper) (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
  case rep of
    PrdRep -> return (Xtor (loc, TyData   PosRep (Just (data_name decl)) [MkXtorSig xt substTypes]) rep xt substInferred)
    CnsRep -> return (Xtor (loc, TyCodata NegRep (Just (data_name decl)) [MkXtorSig xt substTypes]) rep xt substInferred)
--
-- Structural pattern and copattern matches:
--
genConstraintsTerm (XMatch loc rep Structural cases) = do
  inferredCases <- forM cases (\MkCmdCase{cmdcase_args, cmdcase_name, cmdcase_ext, cmdcase_cmd} -> do
                      -- Generate positive and negative unification variables for all variables
                      -- bound in the pattern.
                      (uvarsPos, uvarsNeg) <- freshTVars cmdcase_args
                      -- Check the command in the context extended with the positive unification variables
                      cmdInferred <- withContext uvarsPos (genConstraintsCommand cmdcase_cmd)
                      -- Return the negative unification variables in the returned type.
                      return (MkCmdCase cmdcase_ext cmdcase_name cmdcase_args cmdInferred, MkXtorSig cmdcase_name uvarsNeg))
  case rep of
    -- The return type is a structural type consisting of a XtorSig for each case.
    PrdRep -> return $ XMatch (loc, TyCodata PosRep Nothing (snd <$> inferredCases)) rep Structural (fst <$> inferredCases)
    CnsRep -> return $ XMatch (loc, TyData   NegRep Nothing (snd <$> inferredCases)) rep Structural (fst <$> inferredCases)
--
-- Nominal pattern and copattern matches:
--
genConstraintsTerm (XMatch _ _ Nominal []) =
  -- We know that empty matches cannot be parsed as nominal.
  throwGenError ["Unreachable: A nominal match needs to have at least one case."]
genConstraintsTerm (XMatch loc rep Nominal cases@(pmcase:_)) = do
  -- We lookup the data declaration based on the first pattern match case.
  decl <- lookupDataDecl (cmdcase_name pmcase)
  -- We check that all cases in the pattern match belong to the type declaration.
  checkCorrectness (cmdcase_name <$> cases) decl
  -- We check that all xtors in the type declaration are matched against.
  checkExhaustiveness (cmdcase_name <$> cases) decl
  inferredCases <- forM cases (\MkCmdCase {..} -> do
                  -- We lookup the types belonging to the xtor in the type declaration.
                   posTypes <- sig_args <$> lookupXtorSig cmdcase_name PosRep
                   negTypes <- sig_args <$> lookupXtorSig cmdcase_name NegRep
                   -- We generate constraints for the command in the context extended
                   -- with the types from the signature.
                   cmdInferred <- withContext posTypes (genConstraintsCommand cmdcase_cmd)
                   return (MkCmdCase cmdcase_ext cmdcase_name cmdcase_args cmdInferred, MkXtorSig cmdcase_name negTypes))
  case rep of
    PrdRep -> return $ XMatch (loc, TyNominal PosRep Nothing (data_name decl)) rep Nominal (fst <$> inferredCases)
    CnsRep -> return $ XMatch (loc, TyNominal NegRep Nothing (data_name decl)) rep Nominal (fst <$> inferredCases)
--
-- Refinement inference
--
genConstraintsTerm (XMatch _ _ Refinement []) =
  -- We know that empty matches cannot be parsed as refinement.
  throwGenError ["Unreachable: A nominal match needs to have at least one case."]
genConstraintsTerm (XMatch loc rep Refinement cases@(pmcase:_)) = do
  -- We lookup the data declaration based on the first pattern match case.
  decl <- lookupDataDecl (cmdcase_name pmcase)
  -- We check that all cases in the pattern match belong to the type declaration.
  checkCorrectness (cmdcase_name <$> cases) decl
  inferredCases <- forM cases (\MkCmdCase {..} -> do
                       -- Generate positive and negative unification variables for all variables
                       -- bound in the pattern.
                       (uvarsPos, uvarsNeg) <- freshTVars cmdcase_args
                       -- Check the command in the context extended with the positive unification variables
                       cmdInferred <- withContext uvarsPos (genConstraintsCommand cmdcase_cmd)
                       -- We have to bound the unification variables with the lower and upper bounds generated
                       -- from the information in the type declaration. These lower and upper bounds correspond
                       -- to the least and greatest type translation.
                       lowerBound <- sig_args <$> (translateXtorSigLower =<< lookupXtorSig cmdcase_name PosRep)
                       upperBound <- sig_args <$> (translateXtorSigUpper =<< lookupXtorSig cmdcase_name NegRep)
                       genConstraintsCtxts lowerBound uvarsNeg (PatternMatchConstraint loc)
                       genConstraintsCtxts uvarsPos upperBound (PatternMatchConstraint loc)
                       -- For the type, we return the unification variables which are now bounded by the least
                       -- and greatest type translation.
                       return (MkCmdCase cmdcase_ext cmdcase_name cmdcase_args cmdInferred, MkXtorSig cmdcase_name uvarsNeg))
  case rep of
    PrdRep -> return $ XMatch (loc, TyCodata PosRep (Just (data_name decl)) (snd <$> inferredCases)) rep Nominal (fst <$> inferredCases)
    CnsRep -> return $ XMatch (loc, TyData   NegRep (Just (data_name decl)) (snd <$> inferredCases)) rep Nominal (fst <$> inferredCases)
--
-- Mu and TildeMu abstractions:
--
genConstraintsTerm (MuAbs loc PrdRep bs cmd) = do
  (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
  cmdInferred <- withContext [PrdCnsType CnsRep uvneg] (genConstraintsCommand cmd)
  return (MuAbs (loc, uvpos) PrdRep bs cmdInferred)
genConstraintsTerm (MuAbs loc CnsRep bs cmd) = do
  (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
  cmdInferred <- withContext [PrdCnsType PrdRep uvpos] (genConstraintsCommand cmd)
  return (MuAbs (loc, uvneg) CnsRep bs cmdInferred)
--
-- Structural Destructor Application (Syntactic Sugar):
--
-- e.'D subst
--
genConstraintsTerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Structural } destructee (subst1,PrdRep,subst2)) = do
  -- Infer the types of the arguments to the destructor.
  subst1Inferred <- genConstraintsSubst subst1
  subst2Inferred <- genConstraintsSubst subst2
  -- Infer the type of the destructee.
  destructeeInferred <- genConstraintsTerm destructee
  -- Generate a unification variable for the return type.
  (retTypePos, retTypeNeg) <- freshTVar (DtorAp loc)
  -- The type at which the destructor call happens is constructed from the
  -- (inferred) return type and the inferred types from the argument list
  let lctxt = getTypArgs subst1Inferred ++ [PrdCnsType CnsRep retTypeNeg] ++ getTypArgs subst2Inferred
  let codataType = TyCodata NegRep Nothing [MkXtorSig xt lctxt]
  -- The type of the destructee must be a subtype of the Destructor type just generated.
  addConstraint (SubType (DtorApConstraint loc) (getTypeTerm destructeeInferred) codataType)
  return (Dtor (loc,retTypePos) xt destructeeInferred (subst1Inferred,PrdRep,subst2Inferred))
genConstraintsTerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Structural } destructee (subst1,CnsRep,subst2)) = do
  -- Infer the types of the arguments to the destructor.
  subst1Inferred <- genConstraintsSubst subst1
  subst2Inferred <- genConstraintsSubst subst2
  -- Infer the type of the destructee.
  destructeeInferred <- genConstraintsTerm destructee
  -- Generate a unification variable for the return type.
  (retTypePos, retTypeNeg) <- freshTVar (DtorAp loc)
  -- The type at which the destructor call happens is constructed from the
  -- (inferred) return type and the inferred types from the argument list
  let lctxt = getTypArgs subst1Inferred ++ [PrdCnsType PrdRep retTypePos] ++ getTypArgs subst2Inferred
  let codataType = TyCodata NegRep Nothing [MkXtorSig xt lctxt]
  -- The type of the destructee must be a subtype of the Destructor type just generated.
  addConstraint (SubType (DtorApConstraint loc) (getTypeTerm destructeeInferred) codataType)
  return (Dtor (loc,retTypeNeg) xt destructeeInferred (subst1Inferred,CnsRep,subst2Inferred))
--
-- Nominal Destructor Application (Syntactic Sugar):
--
-- e.D subst
--
genConstraintsTerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Nominal } destructee (subst1,PrdRep,subst2)) = do
  -- Infer the types of the arguments to the destructor.
  subst1Inferred <- genConstraintsSubst subst1
  subst2Inferred <- genConstraintsSubst subst2
  -- Infer the type of the destructee.
  destructeeInferred <- genConstraintsTerm destructee
  -- Look up the data declaration and the xtorSig.
  decl <- lookupDataDecl xt
  let ty = TyNominal NegRep Nothing (data_name decl)
  xtorSig <- lookupXtorSig xt NegRep
  -- The type of the destructee must be a subtype of the nominal type.
  addConstraint (SubType (DtorApConstraint loc) (getTypeTerm destructeeInferred) ty)
  -- Split the argument list into the explicit arguments and the implicit argument.
  -- The return type is the implicit element in the xtorSig, which must be a CnsType.
  let (tys1,retType, tys2) = splitContext (length subst1) CnsRep (sig_args xtorSig)
  -- The argument types must be subtypes of the types declared in the xtorSig.
  genConstraintsCtxts (getTypArgs (subst1Inferred ++ subst2Inferred)) (tys1 ++ tys2) (DtorArgsConstraint loc)
  return (Dtor (loc,retType) xt destructeeInferred (subst1Inferred,PrdRep,subst2Inferred))
genConstraintsTerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Nominal } destructee (subst1,CnsRep,subst2)) = do
  -- Infer the types of the arguments to the destructor.
  subst1Inferred <- genConstraintsSubst subst1
  subst2Inferred <- genConstraintsSubst subst2
  -- Infer the type of the destructee.
  destructeeInferred <- genConstraintsTerm destructee
  -- Look up the data declaration and the xtorSig.
  decl <- lookupDataDecl xt
  let ty = TyNominal NegRep Nothing (data_name decl)
  xtorSig <- lookupXtorSig xt NegRep
  -- The type of the destructee must be a subtype of the nominal type.
  addConstraint (SubType (DtorApConstraint loc) (getTypeTerm destructeeInferred) ty)
  -- Split the argument list into the explicit and implicit arguments. (Implicit argument in the middle)
  -- The return type is the implicit element in the xtorSig, which must be a PrdType.
  let (tys1,retType, tys2) = splitContext (length subst1) PrdRep (sig_args xtorSig)
  -- The argument types must be subtypes of the types declared in the xtorSig.
  genConstraintsCtxts (getTypArgs (subst1Inferred ++ subst2Inferred)) (tys1 ++ tys2) (DtorArgsConstraint loc)
  return (Dtor (loc,retType) xt destructeeInferred (subst1Inferred,CnsRep,subst2Inferred))
--
-- Refinement Destructor Application (Syntactic Sugar):
--
-- e.D subst
--
genConstraintsTerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Refinement } destructee (subst1,PrdRep,subst2)) = do
  -- Infer the types of the arguments to the destructor.
  subst1Inferred <- genConstraintsSubst subst1
  subst2Inferred <- genConstraintsSubst subst2
  -- Infer the type of the destructee.
  destructeeInferred <- genConstraintsTerm destructee
  -- Look up the data declaration and the xtorSig.
  -- The type as well as the xtorSig have to be translated.
  decl <- lookupDataDecl xt
  -- Generate a unification variable for the return type.
  (retTypePos, retTypeNeg) <- freshTVar (DtorAp loc)
  -- The type at which the destructor call happens is constructed from the
  -- (inferred) return type and the inferred types from the argument list
  let lctxt = getTypArgs subst1Inferred ++ [PrdCnsType CnsRep retTypeNeg] ++ getTypArgs subst2Inferred
  let codataType = TyCodata NegRep (Just (data_name decl)) [MkXtorSig xt lctxt]
  -- The type of the destructee must be a subtype of the translated nominal type.
  addConstraint (SubType (DtorApConstraint loc) (getTypeTerm destructeeInferred) codataType)
  -- The xtor sig has to be translated.
  xtorSigTranslated <- translateXtorSigUpper =<< lookupXtorSig xt NegRep
  -- Split the argument list into the explicit and implicit arguments. (Implicit argument in the middle)
  let (tys1,_retType, tys2) = splitContext (length subst1) CnsRep (sig_args xtorSigTranslated)
  -- The argument types must be subtypes of the greatest translation of the xtor sig.
  genConstraintsCtxts (getTypArgs (subst1Inferred ++ subst2Inferred)) (tys1 ++ tys2) (DtorArgsConstraint loc)
  return (Dtor (loc,retTypePos) xt destructeeInferred (subst1Inferred,PrdRep,subst2Inferred))
genConstraintsTerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Refinement } destructee (subst1,CnsRep,subst2)) = do
  -- Infer the types of the arguments to the destructor.
  subst1Inferred <- genConstraintsSubst subst1
  subst2Inferred <- genConstraintsSubst subst2
  -- Infer the type of the destructee.
  destructeeInferred <- genConstraintsTerm destructee
  -- Look up the data declaration and the xtorSig.
  -- The type as well as the xtorSig have to be translated.
  decl <- lookupDataDecl xt
  -- Generate a unification variable for the return type.
  (retTypePos, retTypeNeg) <- freshTVar (DtorAp loc)
  -- The type at which the destructor call happens is constructed from the
  -- (inferred) return type and the inferred types from the argument list
  let lctxt = getTypArgs subst1Inferred ++ [PrdCnsType PrdRep retTypePos] ++ getTypArgs subst2Inferred
  let codataType = TyCodata NegRep (Just (data_name decl)) [MkXtorSig xt lctxt]
  -- The type of the destructee must be a subtype of the translated nominal type.
  addConstraint (SubType (DtorApConstraint loc) (getTypeTerm destructeeInferred) codataType)
  -- The xtor sig has to be translated.
  xtorSigTranslated <- translateXtorSigUpper =<< lookupXtorSig xt NegRep
  -- Split the argument list into the explicit and implicit arguments. (Implicit argument in the middle)
  let (tys1,_retType, tys2) = splitContext (length subst1) PrdRep (sig_args xtorSigTranslated)
  -- The argument types must be subtypes of the greatest translation of the xtor sig.
  genConstraintsCtxts (getTypArgs (subst1Inferred ++ subst2Inferred)) (tys1 ++ tys2) (DtorArgsConstraint loc)
  return (Dtor (loc,retTypeNeg) xt destructeeInferred (subst1Inferred,CnsRep,subst2Inferred))
--
--
-- Structural Match (Syntactic Sugar):
--
-- case e of { 'X(xs) => e' }
--
genConstraintsTerm (Case loc Structural destructee cases) = do
  destructeeInferred <- genConstraintsTerm destructee
  -- Generate a unification variable for the return type of the pattern match
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  casesInferred <- forM cases $ \MkTermCase { tmcase_ext, tmcase_name, tmcase_args, tmcase_term } -> do
    -- Generate positive and negative unification variables for all variables
    -- bound in the pattern.
    (argtsPos,argtsNeg) <- freshTVars tmcase_args
    -- Type case term in context extended with new unification variables
    tmcase_termInferred <- withContext argtsPos (genConstraintsTerm tmcase_term)
    -- The inferred type of the term must be a subtype of the pattern match return type
    addConstraint (SubType (CaseConstraint tmcase_ext) (getTypeTerm tmcase_termInferred) retTypeNeg)
    return (MkTermCase tmcase_ext tmcase_name tmcase_args tmcase_termInferred, MkXtorSig tmcase_name argtsNeg)
  -- The type of the pattern match destructee must be a subtype of the type generated by the match.
  addConstraint (SubType (PatternMatchConstraint loc) (getTypeTerm destructeeInferred) (TyData NegRep Nothing (snd <$> casesInferred)))
  return (Case (loc, retTypePos) Structural destructeeInferred (fst <$> casesInferred))
--
-- Nominal Match (Syntactic Sugar):
--
-- case e of { X(xs) => e' }
--
genConstraintsTerm (Case _ Nominal _ []) =
  -- We know that empty matches cannot be parsed as nominal.
  -- It is therefore safe to pattern match on the head of the xtors in the other cases.
  throwGenError ["Unreachable: A nominal match needs to have at least one case."]
genConstraintsTerm (Case loc Nominal destructee cases@(MkTermCase { tmcase_name = xtn }:_)) = do
  destructeeInferred <- genConstraintsTerm destructee
  -- Lookup the type declaration in the context.
  tn@NominalDecl{..} <- lookupDataDecl xtn
  -- We check that all cases in the pattern match belong to the type declaration.
  checkCorrectness (tmcase_name <$> cases) tn
  -- We check that all xtors in the type declaration are matched against.
  checkExhaustiveness (tmcase_name <$> cases) tn
  -- We check that the destructee is a subtype of the Nominal Type.
  addConstraint (SubType (PatternMatchConstraint loc) (getTypeTerm destructeeInferred) (TyNominal NegRep Nothing data_name))
  -- We generate a unification variable for the return type.
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  casesInferred <- forM cases $ \MkTermCase { tmcase_ext, tmcase_name, tmcase_args, tmcase_term } -> do
    -- We look up the argument types of the xtor
    posTypes <- sig_args <$> lookupXtorSig tmcase_name PosRep
    -- Type case term using new type vars
    tmcase_termInferred <- withContext posTypes (genConstraintsTerm tmcase_term)
    -- The term must have a subtype of the pattern match return type
    addConstraint (SubType (CaseConstraint tmcase_ext) (getTypeTerm tmcase_termInferred) retTypeNeg)
    return (MkTermCase tmcase_ext tmcase_name tmcase_args tmcase_termInferred)
  return (Case (loc,retTypePos) Nominal destructeeInferred casesInferred)
--
-- Refinement Match (Syntactic Sugar):
--
-- case e of { X(xs) => e' }
--
genConstraintsTerm (Case _ Refinement _ []) =
  -- We know that empty matches cannot be parsed as nominal.
  -- It is therefore safe to pattern match on the head of the xtors in the other cases.
  throwGenError ["Unreachable: A nominal match needs to have at least one case."]
genConstraintsTerm (Case loc Refinement destructee cases@(MkTermCase { tmcase_name = xtn }:_)) = do
  destructeeInferred <- genConstraintsTerm destructee
  -- Lookup the type declaration in the context.
  tn@NominalDecl{..} <- lookupDataDecl xtn
  -- We check that all cases in the pattern match belong to the type declaration.
  checkCorrectness (tmcase_name <$> cases) tn
  -- We generate a unification variable for the return type.
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  casesInferred <- forM cases $ \MkTermCase { tmcase_ext, tmcase_name, tmcase_args, tmcase_term } -> do
    -- Generate unification variables for each case arg
    (argtsPos,argtsNeg) <- freshTVars tmcase_args
    -- Typecheck case term using new unification vars
    tmcase_termInferred <- withContext argtsPos (genConstraintsTerm tmcase_term)
    -- The term must have a subtype of the pattern match return type
    addConstraint (SubType (CaseConstraint tmcase_ext) (getTypeTerm tmcase_termInferred) retTypeNeg)
    -- We have to bound the unification variables with the lower and upper bounds generated
    -- from the information in the type declaration. These lower and upper bounds correspond
    -- to the least and greatest type translation.
    lowerBound <- sig_args <$> (translateXtorSigLower =<< lookupXtorSig tmcase_name PosRep)
    upperBound <- sig_args <$> (translateXtorSigUpper =<< lookupXtorSig tmcase_name NegRep)
    genConstraintsCtxts lowerBound argtsNeg (PatternMatchConstraint loc)
    genConstraintsCtxts argtsPos upperBound (PatternMatchConstraint loc)
    return (MkTermCase tmcase_ext tmcase_name tmcase_args tmcase_termInferred, MkXtorSig tmcase_name argtsNeg)
  --  The destructee must have a subtype of the refinement type constructed from the cases.
  addConstraint (SubType (PatternMatchConstraint loc) (getTypeTerm destructeeInferred) (TyData NegRep (Just data_name) (snd <$> casesInferred)))
  return (Case (loc,retTypePos) Nominal destructeeInferred (fst <$> casesInferred))
--
-- Structural Comatch (Syntactic Sugar):
--
-- cocase { 'X(xs) => e' }
--
genConstraintsTerm (Cocase loc Structural cocases) = do
  cocasesInferred <- forM cocases $ \MkTermCaseI { tmcasei_ext, tmcasei_name, tmcasei_args = (as1, (), as2), tmcasei_term } -> do
    -- Generate unification variables for each case arg
    (argtsPos1,argtsNeg1) <- freshTVars as1
    (argtsPos2,argtsNeg2) <- freshTVars as2
    -- Typecheck the term in the context extended with the unification variables.
    -- HACK: `tmcasei_term` needs to be checked in the proper context, i.e. we need to include the implicit variable even though
    -- its type is the type we are actually inferring in this call. Since the variable is implicit, it can never be referenced explicitly.
    -- Hence, the "*" type variable just serves as a placeholder to ensure that the arguments have the correct De-Bruijn indices.
    tmcasei_termInferred <- withContext (argtsPos1 ++ [PrdCnsType CnsRep (TyVar NegRep Nothing (MkTVar "*"))] ++ argtsPos2) (genConstraintsTerm tmcasei_term)
    return (MkTermCaseI tmcasei_ext tmcasei_name (as1, (), as2) tmcasei_termInferred, MkXtorSig tmcasei_name (argtsNeg1 ++ [PrdCnsType CnsRep $ getTypeTerm tmcasei_termInferred] ++ argtsNeg2))
  return (Cocase (loc,TyCodata PosRep Nothing (snd <$> cocasesInferred)) Structural (fst <$> cocasesInferred))
--
-- Nominal Comatch (Syntactic Sugar):
--
-- cocase { X(xs) => e' }
--
genConstraintsTerm (Cocase _ Nominal []) =
  throwGenError ["Unreachable: A nominal comatch needs to have at least one case."]
genConstraintsTerm (Cocase loc Nominal cocases@(MkTermCaseI {tmcasei_name = xtn}:_)) = do
  -- Lookup the type declaration in the context.
  tn@NominalDecl{..} <- lookupDataDecl xtn
  -- We check that all cases in the copattern match belong to the type declaration.
  checkCorrectness (tmcasei_name <$> cocases) tn
  -- We check that all xtors in the type declaration are matched against.
  checkExhaustiveness (tmcasei_name <$> cocases) tn
  cocasesInferred <- forM cocases $ \MkTermCaseI { tmcasei_ext, tmcasei_name, tmcasei_args, tmcasei_term } -> do
    -- We look up the argument types of the xtor
    posTypes <- sig_args <$> lookupXtorSig tmcasei_name PosRep
    -- Type case term using new type vars
    tmcasei_termInferred <- withContext (init posTypes) (genConstraintsTerm tmcasei_term)
    -- The return type is the last element in the xtorSig, which must be a CnsType.
    let retType = case last posTypes of
                   (PrdCnsType PrdRep _)  -> error "Boom"
                   (PrdCnsType CnsRep ty) -> ty
    -- The term must have a subtype of the copattern match return type
    addConstraint (SubType (CaseConstraint loc) (getTypeTerm tmcasei_termInferred) retType)
    return (MkTermCaseI tmcasei_ext tmcasei_name tmcasei_args tmcasei_termInferred)
  return (Cocase (loc, TyNominal PosRep Nothing data_name) Nominal cocasesInferred)
--
-- Refinement Comatch (Syntactic Sugar):
--
-- cocase { X(xs) => e' }
--
genConstraintsTerm (Cocase _ Refinement []) =
  throwGenError ["Unreachable: A nominal comatch needs to have at least one case."]
genConstraintsTerm (Cocase loc Refinement cocases@(MkTermCaseI {tmcasei_name = xtn}:_)) = do
  -- Lookup the type declaration in the context.
  tn@NominalDecl{..} <- lookupDataDecl xtn
  -- We check that all cases in the pattern match belong to the type declaration.
  checkCorrectness (tmcasei_name <$> cocases) tn
  cocasesInferred <- forM cocases $ \MkTermCaseI { tmcasei_ext, tmcasei_name, tmcasei_args = (as1, (), as2), tmcasei_term } -> do
    -- Generate unification variables for each case arg
    (argtsPos1, argtsNeg1) <- freshTVars as1
    (argtsPos2, argtsNeg2) <- freshTVars as2

    -- HACK: `tmcasei_term` needs to be checked in the proper context, i.e. we need to include the implicit variable even though
    -- its type is the type we are actually inferring in this call. Since the variable is implicit, it can never be referenced explicitly.
    -- Hence, the "*" type variable just serves as a placeholder to ensure that the arguments have the correct De-Bruijn indices.
    let argtsPos = argtsPos1 ++ [PrdCnsType CnsRep (TyVar NegRep Nothing (MkTVar "*"))] ++ argtsPos2

    -- Typecheck case term using new unification vars
    tmcasei_termInferred <- withContext argtsPos (genConstraintsTerm tmcasei_term)
    -- We have to bound the unification variables with the lower and upper bounds generated
    -- from the information in the type declaration. These lower and upper bounds correspond
    -- to the least and greatest type translation.
    lowerBound <- sig_args <$> (translateXtorSigLower =<< lookupXtorSig tmcasei_name PosRep)
    upperBound <- sig_args <$> (translateXtorSigUpper =<< lookupXtorSig tmcasei_name NegRep)

    -- HACK: Split the argument list into the explicit (lb1, lb2) and implicit arguments (_lbi). (Implicit argument in the middle)
    let (lb1, retType, lb2) = splitContext (length as1) CnsRep lowerBound
    -- HACK: Split the argument list into the explicit (ub1, ub2) and implicit arguments (_ubi). (Implicit argument in the middle)
    let (ub1, _ubi, ub2) = splitContext (length as1) CnsRep upperBound

    genConstraintsCtxts (lb1 ++ lb2) (argtsNeg1 ++ argtsNeg2) (PatternMatchConstraint loc)
    genConstraintsCtxts (argtsPos1 ++ argtsPos2) (ub1 ++ ub2) (PatternMatchConstraint loc)

    -- The term must have a subtype of the copattern match return type
    addConstraint (SubType (CaseConstraint loc) (getTypeTerm tmcasei_termInferred) retType)
    return (MkTermCaseI tmcasei_ext tmcasei_name (as1, (), as2) tmcasei_termInferred,
      MkXtorSig tmcasei_name (argtsNeg1 ++ [PrdCnsType CnsRep $ getTypeTerm tmcasei_termInferred] ++ argtsNeg2))
  return (Cocase (loc, TyCodata  PosRep (Just data_name) (snd <$> cocasesInferred)) Nominal (fst <$> cocasesInferred))

genConstraintsCommand :: Command Parsed -> GenM (Command Inferred)
genConstraintsCommand (Done loc) = return (Done loc)
genConstraintsCommand (Call loc fv) = do
  -- Ensure that the referenced command is in scope
  _ <- lookupCommand fv
  return (Call loc fv)
genConstraintsCommand (Print loc prd cmd) = do
  prd' <- genConstraintsTerm prd
  cmd' <- genConstraintsCommand cmd
  return (Print loc prd' cmd')
genConstraintsCommand (Read loc cns) = do
  cns' <- genConstraintsTerm cns
  addConstraint (SubType (ReadConstraint loc)  (TyNominal PosRep Nothing (MkTypeName "Nat")) (getTypeTerm cns'))
  return (Read loc cns')
genConstraintsCommand (Apply loc kind t1 t2) = do
  t1' <- genConstraintsTerm t1
  t2' <- genConstraintsTerm t2
  addConstraint (SubType (CommandConstraint loc) (getTypeTerm t1') (getTypeTerm t2'))
  return (Apply loc kind t1' t2')

---------------------------------------------------------------------------------------------
-- Checking recursive terms
---------------------------------------------------------------------------------------------

genConstraintsTermRecursive :: Loc
                            -> FreeVarName
                            -> PrdCnsRep pc -> Term pc Parsed
                            -> GenM (Term pc Inferred)
genConstraintsTermRecursive loc fv PrdRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  tm <- withTerm PrdRep fv (FreeVar (loc, x) PrdRep fv) loc (TypeScheme [] x) (genConstraintsTerm tm)
  addConstraint (SubType RecursionConstraint (getTypeTerm tm) y)
  return tm
genConstraintsTermRecursive loc fv CnsRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  tm <- withTerm CnsRep fv (FreeVar (loc,y) CnsRep fv) loc (TypeScheme [] y) (genConstraintsTerm tm)
  addConstraint (SubType RecursionConstraint x (getTypeTerm tm))
  return tm

