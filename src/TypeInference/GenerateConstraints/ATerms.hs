module TypeInference.GenerateConstraints.ATerms
  ( genConstraintsATerm
  , genConstraintsATermRecursive
  ) where

import Control.Monad (forM, forM_, when)

import Pretty.ATerms ()
import Pretty.Types ()
import Syntax.ATerms
import Syntax.Types
import TypeInference.GenerateConstraints.Definition
import Utils

---------------------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------------------

-- | Every asymmetric terms gets assigned a positive type.
genConstraintsATerm :: InferenceMode
                    -> ATerm Loc FreeVarName
                    -> GenM ( ATerm () FreeVarName
                            , Typ Pos)
genConstraintsATerm _ (BVar _ idx) = do
  ty <- lookupContext PrdRep idx
  return (BVar () idx, ty)
genConstraintsATerm _ (FVar loc fv) = do
  tys <- lookupDefEnv fv
  ty <- instantiateTypeScheme fv loc tys
  return (FVar () fv, ty)

genConstraintsATerm im (Ctor _ xt@MkXtorName { xtorNominalStructural = Structural } args) = do
  args' <- sequence (genConstraintsATerm im <$> args)
  let ty = TyData PosRep [MkXtorSig xt (MkTypArgs (snd <$> args') [])]
  return (Ctor () xt (fst <$> args'), ty)
genConstraintsATerm im (Ctor loc xt@MkXtorName { xtorNominalStructural = Nominal } args) = do
  args' <- sequence (genConstraintsATerm im <$> args)
  tn <- lookupDataDecl xt
  xtorSig <- lookupXtorSig tn xt NegRep
  when (length args' /= length (prdTypes $ sig_args xtorSig)) $
    throwGenError $ "Ctor " ++ unXtorName xt ++ " called with incorrect number of arguments"
  forM_ (zip args' (prdTypes $ sig_args xtorSig)) $ \((_,t1),t2) -> addConstraint $ SubType (CtorArgsConstraint loc) t1 t2
  let ty = if im == InferNominal then TyNominal PosRep (data_name tn)
      else TyRefined PosRep (data_name tn) $ TyData PosRep [MkXtorSig xt $ MkTypArgs (snd <$> args') [] ]
  return (Ctor () xt (fst <$> args'), ty)
  
genConstraintsATerm im (Dtor loc xt@MkXtorName { xtorNominalStructural = Structural } t args) = do
  args' <- sequence (genConstraintsATerm im <$> args)
  (retTypePos, retTypeNeg) <- freshTVar (DtorAp loc)
  let codataType = TyCodata NegRep [MkXtorSig xt (MkTypArgs (snd <$> args') [retTypeNeg])]
  (t', ty') <- genConstraintsATerm im t
  addConstraint (SubType (DtorApConstraint loc) ty' codataType)
  return (Dtor () xt t' (fst <$> args'), retTypePos)
genConstraintsATerm im (Dtor loc xt@MkXtorName { xtorNominalStructural = Nominal } t args) = do
  args' <- sequence (genConstraintsATerm im <$> args)
  tn <- lookupDataDecl xt
  (t', ty') <- genConstraintsATerm im t
  addConstraint (SubType (DtorApConstraint loc) ty' (TyNominal NegRep (data_name tn)) )
  xtorSig <- lookupXtorSig tn xt NegRep
  when (length args' /= length (prdTypes $ sig_args xtorSig)) $
    throwGenError $ "Dtor " ++ unXtorName xt ++ " called with incorrect number of arguments"
  forM_ (zip args' (prdTypes $ sig_args xtorSig)) $ \((_,t1),t2) -> addConstraint $ SubType (DtorArgsConstraint loc) t1 t2
  return (Dtor () xt t' (fst <$> args'), head $ cnsTypes $ sig_args xtorSig)

{-
match t with { X_1(x_1,...,x_n) => e_1, ... }

If X_1 has nominal type N, then:
- T <: N for t:T
- All X_i must be constructors of type N (correctness)
- All constructors of type N must appear in match (exhaustiveness)
- All e_i must have same type, this is the return type
- Types of x_1,...,x_n in e_i must correspond with types in declaration of X_i
-}
genConstraintsATerm im (Match loc t cases@(MkACase _ xtn@(MkXtorName Nominal _) _ _:_)) = do
  (t', matchType) <- genConstraintsATerm im t
  tn <- lookupDataDecl xtn
  -- Only check exhaustiveness when not using refinements
  when (im == InferNominal) $ checkExhaustiveness (acase_name <$> cases) tn
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  cases' <- sequence (genConstraintsATermCase im retTypeNeg <$> cases)
  forM_ (zip (data_xtors tn PosRep) cases') $ \(xts1,(_,xts2)) -> genConstraintsACaseArgs xts1 xts2 loc
  let ty = if im == InferNominal then TyNominal NegRep (data_name tn)
      else TyRefined NegRep (data_name tn) (TyData NegRep (snd <$> cases'))   
  addConstraint (SubType (PatternMatchConstraint loc) matchType ty)
  return (Match () t' (fst <$> cases') , retTypePos)

genConstraintsATerm im (Match loc t cases) = do
  (t', matchType) <- genConstraintsATerm im t
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  cases' <- sequence (genConstraintsATermCase im retTypeNeg <$> cases)
  addConstraint (SubType (PatternMatchConstraint loc) matchType (TyData NegRep (snd <$> cases')))
  return (Match () t' (fst <$> cases'), retTypePos)

{-
comatch { X_1(x_1,...,x_n) => e_1, ... }

If X_1 has nominal type N, then:
- All X_i must be destructors of type N (correctness)
- All destructors of type N must appear in comatch (exhaustiveness)
- All e_i must have same type, this is the return type
- Types of x_1,...,x_n in e_i must correspond with types in declaration of X_i
-}
genConstraintsATerm im (Comatch loc cocases@(MkACase _ xtn@(MkXtorName Nominal _) _ _:_)) = do
  tn <- lookupDataDecl xtn
  -- Only check exhaustiveness when not using refinements
  when (im == InferNominal) $ checkExhaustiveness (acase_name <$> cocases) tn
  cocases' <- sequence (genConstraintsATermCocase im <$> cocases)
  forM_ (zip (data_xtors tn PosRep) cocases') $ \(xts1,(_,xts2)) -> genConstraintsACaseArgs xts1 xts2 loc
  let ty = if im == InferNominal then TyNominal PosRep (data_name tn) 
      else TyRefined PosRep (data_name tn) (TyCodata PosRep (snd <$> cocases'))
  return (Comatch () (fst <$> cocases'), ty)

genConstraintsATerm im (Comatch _ cocases) = do
  cocases' <- sequence (genConstraintsATermCocase im <$> cocases)
  let ty = TyCodata PosRep (snd <$> cocases')
  return (Comatch () (fst <$> cocases'), ty)

genConstraintsATermCase :: InferenceMode -> Typ Neg
                        -> ACase Loc FreeVarName
                        -> GenM (ACase () FreeVarName, XtorSig Neg)
genConstraintsATermCase im retType MkACase { acase_ext, acase_name, acase_args, acase_term } = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (freshTVar . ProgramVariable)
  (acase_term', retTypeInf) <- withContext (MkTypArgs argtsPos []) (genConstraintsATerm im acase_term)
  addConstraint (SubType (CaseConstraint acase_ext) retTypeInf retType) -- Case type
  return (MkACase () acase_name acase_args acase_term', MkXtorSig acase_name (MkTypArgs argtsNeg []))

genConstraintsATermCocase :: InferenceMode -> ACase Loc FreeVarName
                          -> GenM (ACase () FreeVarName, XtorSig Neg)
genConstraintsATermCocase im MkACase { acase_name, acase_args, acase_term } = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (freshTVar . ProgramVariable)
  (acase_term', retType) <- withContext (MkTypArgs argtsPos []) (genConstraintsATerm im acase_term)
  let sig = MkXtorSig acase_name (MkTypArgs argtsNeg [retType])
  return (MkACase () acase_name acase_args acase_term', sig)

genConstraintsACaseArgs :: XtorSig Pos -> XtorSig Neg -> Loc -> GenM ()
genConstraintsACaseArgs xts1 xts2 loc = do
  let sa1 = sig_args xts1; sa2 = sig_args xts2
  forM_ (zip (prdTypes sa1) (prdTypes sa2)) $ \(pt1,pt2) -> addConstraint $ SubType (PatternMatchConstraint loc) pt1 pt2
  forM_ (zip (cnsTypes sa1) (cnsTypes sa2)) $ \(ct1,ct2) -> addConstraint $ SubType (PatternMatchConstraint loc) ct2 ct1


---------------------------------------------------------------------------------------------
-- Asymmetric Terms with recursive binding
---------------------------------------------------------------------------------------------

genConstraintsATermRecursive :: InferenceMode
                             -> FreeVarName
                             -> ATerm Loc FreeVarName
                             -> GenM (ATerm () FreeVarName, Typ Pos)
genConstraintsATermRecursive im fv tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  (tm, ty) <- withDefEnv fv (FVar () fv) (TypeScheme [] x) (genConstraintsATerm im tm)
  addConstraint (SubType RecursionConstraint ty y)
  return (tm, ty)
