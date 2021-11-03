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
genConstraintsATerm :: ATerm Parsed
                    -> GenM (ATerm Inferred)
genConstraintsATerm (BVar loc idx) = do
  ty <- lookupContext PrdRep idx
  return (BVar (loc, ty) idx)
genConstraintsATerm (FVar loc fv) = do
  tys <- snd <$> lookupATerm fv
  ty <- instantiateTypeScheme fv loc tys
  return (FVar (loc,ty) fv)

genConstraintsATerm (Ctor loc xt@MkXtorName { xtorNominalStructural = Structural } args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  let ty = TyData PosRep Nothing [MkXtorSig xt (MkTypArgs (getTypeATerm <$> args') [])]
  return (Ctor (loc,ty) xt args')
genConstraintsATerm (Ctor loc xt@MkXtorName { xtorNominalStructural = Nominal } args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  tn <- lookupDataDecl xt
  im <- asks (inferMode . snd)
  xtorSig <- case im of
    InferNominal -> lookupXtorSig xt NegRep
    InferRefined -> translateXtorSigFull =<< lookupXtorSig xt NegRep
  when (length args' /= length (prdTypes $ sig_args xtorSig)) $
    throwGenError ["Ctor " <> unXtorName xt <> " called with incorrect number of arguments"]
  -- Nominal type constraint!!
  forM_ (zip args' (prdTypes $ sig_args xtorSig)) $ \(t1,t2) -> addConstraint $ SubType (CtorArgsConstraint loc) (getTypeATerm t1) t2
  let ty = case im of
        InferNominal -> TyNominal PosRep (data_name tn)
        InferRefined -> TyData PosRep (Just $ data_name tn) [MkXtorSig xt $ MkTypArgs (getTypeATerm <$> args') []]
  return (Ctor (loc,ty) xt args')

genConstraintsATerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Structural } t args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  (retTypePos, retTypeNeg) <- freshTVar (DtorAp loc)
  let codataType = TyCodata NegRep Nothing [MkXtorSig xt (MkTypArgs (getTypeATerm <$> args') [retTypeNeg])]
  t' <- genConstraintsATerm t
  addConstraint (SubType (DtorApConstraint loc) (getTypeATerm t') codataType)
  return (Dtor (loc,retTypePos) xt t' args')
genConstraintsATerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Nominal } t args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  tn <- lookupDataDecl xt
  t'<- genConstraintsATerm t
  addConstraint (SubType (DtorApConstraint loc) (getTypeATerm t') (TyNominal NegRep (data_name tn)) )
  im <- asks (inferMode . snd)
  xtorSig <- case im of
    InferNominal -> lookupXtorSig xt NegRep
    InferRefined -> translateXtorSigFull =<< lookupXtorSig xt NegRep
  when (length args' /= length (prdTypes $ sig_args xtorSig)) $
    throwGenError ["Dtor " <> unXtorName xt <> " called with incorrect number of arguments"]
  -- Nominal type constraint!!
  forM_ (zip args' (prdTypes $ sig_args xtorSig)) $ \(t1,t2) -> addConstraint $ SubType (DtorArgsConstraint loc) (getTypeATerm t1) t2
  let retType = head $ cnsTypes $ sig_args xtorSig
  return (Dtor (loc,retType) xt t' args')

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
  t' <- genConstraintsATerm t
  tn@NominalDecl{..} <- lookupDataDecl xtn
  checkCorrectness (acase_name <$> cases) tn
  checkExhaustiveness (acase_name <$> cases) tn
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  (cases',casesXtssNeg,casesXtssPos) <- unzip3 <$> sequence (genConstraintsATermCase retTypeNeg <$> cases)
  im <- asks (inferMode . snd)
  -- Nominal type constraint!!
  case im of
    InferNominal -> genConstraintsACaseArgs casesXtssNeg (data_xtors PosRep) loc
    InferRefined -> do
      xtssEmpty <- mapM translateXtorSigEmpty $ data_xtors PosRep 
      xtssFull <- mapM translateXtorSigFull $ data_xtors NegRep
      genConstraintsACaseArgs casesXtssNeg xtssEmpty loc -- empty refinement as lower bound
      genConstraintsACaseArgs xtssFull casesXtssPos loc -- full refinement as upper bound
  let ty = case im of
        InferNominal -> TyNominal NegRep data_name
        InferRefined -> TyData NegRep (Just data_name) casesXtssNeg
  addConstraint (SubType (PatternMatchConstraint loc) (getTypeATerm t') ty)
  return (Match (loc,retTypePos) t' cases')

genConstraintsATerm (Match loc t cases) = do
  t' <- genConstraintsATerm t
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  (cases',casesXtssNeg,_) <- unzip3 <$> sequence (genConstraintsATermCase retTypeNeg <$> cases)
  addConstraint (SubType (PatternMatchConstraint loc) (getTypeATerm t') (TyData NegRep Nothing casesXtssNeg))
  return (Match (loc, retTypePos) t' cases')

{-
comatch { X_1(x_1,...,x_n) => e_1, ... }

If X_1 has nominal type N, then:
- All X_i must be destructors of type N (correctness)
- All destructors of type N must appear in comatch (exhaustiveness)
- All e_i must have same type, this is the return type
- Types of x_1,...,x_n in e_i must correspond with types in declaration of X_i
-}
genConstraintsATerm (Comatch loc cocases@(MkACase _ xtn@(MkXtorName Nominal _) _ _:_)) = do
  tn@NominalDecl{..} <- lookupDataDecl xtn
  checkCorrectness (acase_name <$> cocases) tn
  checkExhaustiveness (acase_name <$> cocases) tn
  (cocases',cocasesXtssNeg,cocasesXtssPos) <- unzip3 <$> sequence (genConstraintsATermCocase <$> cocases)
  im <- asks (inferMode . snd)
  -- Nominal type constraint!!
  case im of
    InferNominal -> genConstraintsACaseArgs cocasesXtssNeg (data_xtors PosRep) loc
    InferRefined -> do
      xtssEmpty <- mapM translateXtorSigEmpty $ data_xtors PosRep
      xtssFull <- mapM translateXtorSigFull $ data_xtors NegRep
      genConstraintsACaseArgs cocasesXtssNeg xtssEmpty loc -- empty refinement as lower bound
      genConstraintsACaseArgs xtssFull cocasesXtssPos loc -- full refinement as upper bound
  let ty = case im of
        InferNominal -> TyNominal PosRep data_name
        InferRefined -> TyCodata PosRep (Just data_name) cocasesXtssNeg
  return (Comatch (loc, ty) cocases')

genConstraintsATerm (Comatch loc cocases) = do
  (cocases',cocasesXtssNeg,_) <- unzip3 <$> sequence (genConstraintsATermCocase <$> cocases)
  let ty = TyCodata PosRep Nothing cocasesXtssNeg
  return (Comatch (loc,ty) cocases')

genConstraintsATermCase :: Typ Neg
                        -> ACase Parsed
                        -> GenM (ACase Inferred, XtorSig Neg, XtorSig Pos)
genConstraintsATermCase retType MkACase { acase_ext, acase_name, acase_args, acase_term } = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (freshTVar . ProgramVariable . fromMaybeVar) -- Generate type var for each case arg
  acase_term' <- withContext (MkTypArgs argtsPos []) (genConstraintsATerm acase_term) -- Type case term using new type vars
  addConstraint (SubType (CaseConstraint acase_ext) (getTypeATerm acase_term') retType) -- Case type
  let sigNeg = MkXtorSig acase_name (MkTypArgs argtsNeg [])
  let sigPos = MkXtorSig acase_name (MkTypArgs argtsPos [])
  return (MkACase acase_ext acase_name acase_args acase_term', sigNeg, sigPos)

genConstraintsATermCocase :: ACase Parsed
                          -> GenM (ACase Inferred, XtorSig Neg, XtorSig Pos)
genConstraintsATermCocase MkACase { acase_ext, acase_name, acase_args, acase_term } = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (freshTVar . ProgramVariable . fromMaybeVar)
  acase_term'<- withContext (MkTypArgs argtsPos []) (genConstraintsATerm acase_term)
  let sigNeg = MkXtorSig acase_name (MkTypArgs argtsNeg [getTypeATerm acase_term'])
  let sigPos = MkXtorSig acase_name (MkTypArgs argtsPos [])
  return (MkACase acase_ext acase_name acase_args acase_term', sigNeg, sigPos)

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
                             -> ATerm Parsed
                             -> GenM (ATerm Inferred)
genConstraintsATermRecursive loc fv tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  tm <- withATerm fv (FVar (loc,x) fv) loc (TypeScheme [] x) (genConstraintsATerm tm)
  addConstraint (SubType RecursionConstraint (getTypeATerm tm) y)
  return tm
