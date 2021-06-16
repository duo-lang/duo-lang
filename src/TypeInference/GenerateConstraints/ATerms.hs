module TypeInference.GenerateConstraints.ATerms
  ( genConstraintsATerm
  , genConstraintsATermRecursive
  ) where

import Control.Monad.Reader

import Pretty.ATerms ()
import Pretty.Types ()
import Syntax.ATerms
import Syntax.Types
import TypeInference.GenerateConstraints.Definition
import Utils
import Lookup

---------------------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------------------

-- | Every asymmetric terms gets assigned a positive type.
genConstraintsATerm :: ATerm Loc FreeVarName
                    -> GenM ( ATerm () FreeVarName
                            , Typ Pos)
genConstraintsATerm (BVar _ idx) = do
  ty <- lookupContext PrdRep idx
  return (BVar () idx, ty)
genConstraintsATerm (FVar loc fv) = do
  tys <- snd <$> lookupDef fv
  ty <- instantiateTypeScheme fv loc tys
  return (FVar () fv, ty)

genConstraintsATerm (Ctor _ xt@MkXtorName { xtorNominalStructural = Structural } args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  let ty = TyData PosRep [MkXtorSig xt (MkTypArgs (snd <$> args') [])]
  return (Ctor () xt (fst <$> args'), ty)
genConstraintsATerm (Ctor loc xt@MkXtorName { xtorNominalStructural = Nominal } args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  tn <- lookupDataDecl xt
  xtorSig <- lookupXtorSig tn xt NegRep
  when (length args' /= length (prdTypes $ sig_args xtorSig)) $
    throwGenError ["Ctor " <> unXtorName xt <> " called with incorrect number of arguments"]
  forM_ (zip args' (prdTypes $ sig_args xtorSig)) $ \((_,t1),t2) -> addConstraint $ SubType (CtorArgsConstraint loc) t1 t2
  im <- asks (inferMode . snd)
  let ty = case im of
        InferNominal -> TyNominal PosRep (data_name tn)
        InferRefined -> TyRefined PosRep (data_name tn) $ TyData PosRep [MkXtorSig xt $ MkTypArgs (snd <$> args') [] ]
  return (Ctor () xt (fst <$> args'), ty)
  
genConstraintsATerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Structural } t args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  (retTypePos, retTypeNeg) <- freshTVar (DtorAp loc)
  let codataType = TyCodata NegRep [MkXtorSig xt (MkTypArgs (snd <$> args') [retTypeNeg])]
  (t', ty') <- genConstraintsATerm t
  addConstraint (SubType (DtorApConstraint loc) ty' codataType)
  return (Dtor () xt t' (fst <$> args'), retTypePos)
genConstraintsATerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Nominal } t args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  tn <- lookupDataDecl xt
  (t', ty') <- genConstraintsATerm t
  addConstraint (SubType (DtorApConstraint loc) ty' (TyNominal NegRep (data_name tn)) )
  xtorSig <- lookupXtorSig tn xt NegRep
  when (length args' /= length (prdTypes $ sig_args xtorSig)) $
    throwGenError ["Dtor " <> unXtorName xt <> " called with incorrect number of arguments"]
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
genConstraintsATerm (Match loc t cases@(MkACase _ xtn@(MkXtorName Nominal _) _ _:_)) = do
  (t', matchType) <- genConstraintsATerm t
  tn <- lookupDataDecl xtn
  checkExhaustiveness (acase_name <$> cases) tn
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  cases' <- sequence (genConstraintsATermCase retTypeNeg <$> cases)
  forM_ (zip (data_xtors tn PosRep) cases') $ \(xts1,(_,xts2)) -> genConstraintsACaseArgs xts1 xts2 loc
  im <- asks (inferMode . snd)
  let ty = case im of
        InferNominal -> TyNominal NegRep (data_name tn)
        InferRefined -> TyRefined NegRep (data_name tn) (TyData NegRep (snd <$> cases'))
  addConstraint (SubType (PatternMatchConstraint loc) matchType ty)
  return (Match () t' (fst <$> cases') , retTypePos)

genConstraintsATerm (Match loc t cases) = do
  (t', matchType) <- genConstraintsATerm t
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  cases' <- sequence (genConstraintsATermCase retTypeNeg <$> cases)
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
genConstraintsATerm (Comatch loc cocases@(MkACase _ xtn@(MkXtorName Nominal _) _ _:_)) = do
  tn <- lookupDataDecl xtn
  checkExhaustiveness (acase_name <$> cocases) tn
  cocases' <- sequence (genConstraintsATermCocase <$> cocases)
  forM_ (zip (data_xtors tn PosRep) cocases') $ \(xts1,(_,xts2)) -> genConstraintsACaseArgs xts1 xts2 loc
  im <- asks (inferMode . snd)
  let ty = case im of
        InferNominal -> TyNominal PosRep (data_name tn)
        InferRefined -> TyRefined PosRep (data_name tn) (TyCodata PosRep (snd <$> cocases'))
  return (Comatch () (fst <$> cocases'), ty)

genConstraintsATerm (Comatch _ cocases) = do
  cocases' <- sequence (genConstraintsATermCocase <$> cocases)
  let ty = TyCodata PosRep (snd <$> cocases')
  return (Comatch () (fst <$> cocases'), ty)

genConstraintsATermCase :: Typ Neg
                        -> ACase Loc FreeVarName
                        -> GenM (ACase () FreeVarName, XtorSig Neg)
genConstraintsATermCase retType MkACase { acase_ext, acase_name, acase_args, acase_term } = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (freshTVar . ProgramVariable)
  (acase_term', retTypeInf) <- withContext (MkTypArgs argtsPos []) (genConstraintsATerm acase_term)
  addConstraint (SubType (CaseConstraint acase_ext) retTypeInf retType) -- Case type
  return (MkACase () acase_name acase_args acase_term', MkXtorSig acase_name (MkTypArgs argtsNeg []))

genConstraintsATermCocase :: ACase Loc FreeVarName
                          -> GenM (ACase () FreeVarName, XtorSig Neg)
genConstraintsATermCocase MkACase { acase_name, acase_args, acase_term } = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (freshTVar . ProgramVariable)
  (acase_term', retType) <- withContext (MkTypArgs argtsPos []) (genConstraintsATerm acase_term)
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

genConstraintsATermRecursive :: FreeVarName
                             -> ATerm Loc FreeVarName
                             -> GenM (ATerm () FreeVarName, Typ Pos)
genConstraintsATermRecursive fv tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  (tm, ty) <- withDef fv (FVar () fv) (TypeScheme [] x) (genConstraintsATerm tm)
  addConstraint (SubType RecursionConstraint ty y)
  return (tm, ty)
