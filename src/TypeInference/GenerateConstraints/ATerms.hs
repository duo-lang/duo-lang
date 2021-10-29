module TypeInference.GenerateConstraints.ATerms
  ( genConstraintsATerm
  , genConstraintsATermRecursive
  ) where

import Control.Monad.Reader
import Data.List (find)

import Syntax.ATerms
import Syntax.Types
import TypeInference.GenerateConstraints.Definition
import Utils
import Lookup

---------------------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------------------

-- | Every asymmetric terms gets assigned a positive type.
genConstraintsATerm :: ATerm Loc
                    -> GenM ( ATerm ()
                            , Typ Pos)
genConstraintsATerm (BVar _ idx) = do
  ty <- lookupContext PrdRep idx
  return (BVar () idx, ty)
genConstraintsATerm (FVar loc fv) = do
  tys <- snd <$> lookupATerm fv
  ty <- instantiateTypeScheme fv loc tys
  return (FVar () fv, ty)

genConstraintsATerm (Ctor _ xt@MkXtorName { xtorNominalStructural = Structural } args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  let ty = TyData PosRep Nothing [MkXtorSig xt (MkTypArgs (snd <$> args') [])]
  return (Ctor () xt (fst <$> args'), ty)
genConstraintsATerm (Ctor loc xt@MkXtorName { xtorNominalStructural = Nominal } args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  tn <- lookupDataDecl xt
  im <- asks (inferMode . snd)
  xtorSig <- case im of
    InferNominal -> lookupXtorSig xt NegRep
    InferRefined -> translateXtorSig =<< lookupXtorSig xt NegRep
  when (length args' /= length (prdTypes $ sig_args xtorSig)) $
    throwGenError ["Ctor " <> unXtorName xt <> " called with incorrect number of arguments"]
  -- Nominal type constraint!!
  forM_ (zip args' (prdTypes $ sig_args xtorSig)) $ \((_,t1),t2) -> addConstraint $ SubType (CtorArgsConstraint loc) t1 t2
  let ty = case im of
        InferNominal -> TyNominal PosRep (data_name tn)
        InferRefined -> TyData PosRep (Just $ data_name tn) [MkXtorSig xt $ MkTypArgs (snd <$> args') []]
  return (Ctor () xt (fst <$> args'), ty)

genConstraintsATerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Structural } t args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  (retTypePos, retTypeNeg) <- freshTVar (DtorAp loc)
  let codataType = TyCodata NegRep Nothing [MkXtorSig xt (MkTypArgs (snd <$> args') [retTypeNeg])]
  (t', ty') <- genConstraintsATerm t
  addConstraint (SubType (DtorApConstraint loc) ty' codataType)
  return (Dtor () xt t' (fst <$> args'), retTypePos)
genConstraintsATerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Nominal } t args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  tn <- lookupDataDecl xt
  (t', ty') <- genConstraintsATerm t
  addConstraint (SubType (DtorApConstraint loc) ty' (TyNominal NegRep (data_name tn)) )
  im <- asks (inferMode . snd)
  xtorSig <- case im of
    InferNominal -> lookupXtorSig xt NegRep
    InferRefined -> translateXtorSig =<< lookupXtorSig xt NegRep
  when (length args' /= length (prdTypes $ sig_args xtorSig)) $
    throwGenError ["Dtor " <> unXtorName xt <> " called with incorrect number of arguments"]
  -- Nominal type constraint!!
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
  checkCorrectness (acase_name <$> cases) tn
  checkExhaustiveness (acase_name <$> cases) tn
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  cases' <- sequence (genConstraintsATermCase retTypeNeg <$> cases)
  im <- asks (inferMode . snd)
  -- Nominal type constraint!!
  xtorSigs <- case im of
    InferNominal -> return $ data_xtors tn PosRep
    InferRefined -> mapM translateXtorSig $ data_xtors tn PosRep
  genConstraintsACaseArgs (snd <$> cases') xtorSigs loc
  let ty = case im of
        InferNominal -> TyNominal NegRep (data_name tn)
        InferRefined -> TyData NegRep (Just $ data_name tn) (snd <$> cases')
  addConstraint (SubType (PatternMatchConstraint loc) matchType ty)
  return (Match () t' (fst <$> cases') , retTypePos)

genConstraintsATerm (Match loc t cases) = do
  (t', matchType) <- genConstraintsATerm t
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  cases' <- sequence (genConstraintsATermCase retTypeNeg <$> cases)
  addConstraint (SubType (PatternMatchConstraint loc) matchType (TyData NegRep Nothing (snd <$> cases')))
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
  checkCorrectness (acase_name <$> cocases) tn
  checkExhaustiveness (acase_name <$> cocases) tn
  cocases' <- sequence (genConstraintsATermCocase <$> cocases)
  im <- asks (inferMode . snd)
  -- Nominal type constraint!!
  xtorSigs <- case im of
    InferNominal -> return $ data_xtors tn PosRep
    InferRefined -> mapM translateXtorSig $ data_xtors tn PosRep
  genConstraintsACaseArgs (snd <$> cocases') xtorSigs loc
  let ty = case im of
        InferNominal -> TyNominal PosRep (data_name tn)
        InferRefined -> TyCodata PosRep (Just $ data_name tn) (snd <$> cocases')
  return (Comatch () (fst <$> cocases'), ty)

genConstraintsATerm (Comatch _ cocases) = do
  cocases' <- sequence (genConstraintsATermCocase <$> cocases)
  let ty = TyCodata PosRep Nothing (snd <$> cocases')
  return (Comatch () (fst <$> cocases'), ty)

genConstraintsATermCase :: Typ Neg
                        -> ACase Loc
                        -> GenM (ACase (), XtorSig Neg)
genConstraintsATermCase retType MkACase { acase_ext, acase_name, acase_args, acase_term } = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (freshTVar . ProgramVariable . fromMaybeVar) -- Generate type var for each case arg
  (acase_term', retTypeInf) <- withContext (MkTypArgs argtsPos []) (genConstraintsATerm acase_term) -- Type case term using new type vars
  addConstraint (SubType (CaseConstraint acase_ext) retTypeInf retType) -- Case type
  return (MkACase () acase_name acase_args acase_term', MkXtorSig acase_name (MkTypArgs argtsNeg []))

genConstraintsATermCocase :: ACase Loc
                          -> GenM (ACase (), XtorSig Neg)
genConstraintsATermCocase MkACase { acase_name, acase_args, acase_term } = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (freshTVar . ProgramVariable . fromMaybeVar)
  (acase_term', retType) <- withContext (MkTypArgs argtsPos []) (genConstraintsATerm acase_term)
  let sig = MkXtorSig acase_name (MkTypArgs argtsNeg [retType])
  return (MkACase () acase_name acase_args acase_term', sig)

genConstraintsACaseArgs :: [XtorSig Neg] -> [XtorSig Pos] -> Loc -> GenM ()
genConstraintsACaseArgs xtsigs1 xtsigs2 loc = do
  forM_ xtsigs1 (\xts1@(MkXtorSig xtn1 _) -> do
    case find (\case (MkXtorSig xtn2 _) -> xtn1==xtn2) xtsigs2 of
      Just xts2 -> do
        let sa1 = sig_args xts1; sa2 = sig_args xts2
        zipWithM_ (\pt1 pt2 -> addConstraint $ SubType (PatternMatchConstraint loc) pt2 pt1) (prdTypes sa1) (prdTypes sa2)
        zipWithM_ (\ct1 ct2 -> addConstraint $ SubType (PatternMatchConstraint loc) ct1 ct2) (cnsTypes sa1) (cnsTypes sa2)
      Nothing -> return ()
    )



---------------------------------------------------------------------------------------------
-- Asymmetric Terms with recursive binding
---------------------------------------------------------------------------------------------

genConstraintsATermRecursive :: Loc 
                             -> FreeVarName
                             -> ATerm Loc
                             -> GenM (ATerm (), Typ Pos)
genConstraintsATermRecursive loc fv tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  (tm, ty) <- withATerm fv (FVar () fv) loc (TypeScheme [] x) (genConstraintsATerm tm)
  addConstraint (SubType RecursionConstraint ty y)
  return (tm, ty)
