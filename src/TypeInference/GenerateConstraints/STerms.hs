module TypeInference.GenerateConstraints.STerms
  ( genConstraintsSTerm
  , genConstraintsSTermRecursive
  , genConstraintsCommand
  ) where

import Control.Monad.Reader
import Data.List (find)
import Pretty.Terms ()
import Pretty.Types ()
import Syntax.Terms
import Syntax.CommonTerm
import Syntax.Types
import TypeInference.GenerateConstraints.Definition
import TypeInference.Constraints
import Utils
import Lookup

---------------------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------------------

genConstraintsArgs :: Substitution Parsed
                   -> GenM (Substitution Inferred)
genConstraintsArgs (MkSubst prdArgs cnsArgs) = do
  prdArgs' <- forM prdArgs genConstraintsSTerm
  cnsArgs' <- forM cnsArgs genConstraintsSTerm
  return (MkSubst prdArgs' cnsArgs')

-- | Generate the constraints for a given STerm.
genConstraintsSTerm :: Term pc Parsed
                    -> GenM (Term pc Inferred)
--
-- Bound variables:
--
-- Bound variables can be looked up in the context.
--
genConstraintsSTerm (BoundVar loc PrdRep idx) = do
  ty <- lookupContext PrdRep idx
  return (BoundVar (loc, ty) PrdRep idx)
genConstraintsSTerm (BoundVar loc CnsRep idx) = do
  ty <- lookupContext CnsRep idx
  return (BoundVar (loc, ty) CnsRep idx)
--
-- Free variables:
--
-- Free variables can be looked up in the environment,
-- where they correspond to typing schemes. This typing
-- scheme has to be instantiated with fresh unification variables.
--
genConstraintsSTerm (FreeVar loc PrdRep v) = do
  tys <- snd <$> lookupSTerm PrdRep v
  ty <- instantiateTypeScheme v loc tys
  return (FreeVar (loc, ty) PrdRep v)
genConstraintsSTerm (FreeVar loc CnsRep v) = do
  tys <- snd <$> lookupSTerm CnsRep v
  ty <- instantiateTypeScheme v loc tys
  return (FreeVar (loc, ty) CnsRep v)
--
-- Xtors
--
genConstraintsSTerm (XtorCall loc rep xt args) = do
  args' <- genConstraintsArgs args
  let argTypes = getTypArgs args'
  case xtorNominalStructural xt of
    Structural -> do
      case rep of
        PrdRep -> return $ XtorCall (loc, TyData   PosRep Nothing [MkXtorSig xt (getTypArgs args')]) rep xt args'
        CnsRep -> return $ XtorCall (loc, TyCodata NegRep Nothing [MkXtorSig xt (getTypArgs args')]) rep xt args'
    Nominal -> do
      tn <- lookupDataDecl xt
      im <- asks (inferMode . snd)
      -- Check if args of xtor are correct
      xtorSig <- case im of
        InferNominal -> lookupXtorSig xt NegRep
        InferRefined -> translateXtorSigUpper =<< lookupXtorSig xt NegRep
      forM_ (zip (prdTypes argTypes) (prdTypes $ sig_args xtorSig)) $ \(t1,t2) -> do
        addConstraint $ SubType (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc }) t1 t2
      case (im, rep) of
            (InferNominal,PrdRep) -> return (XtorCall (loc, TyNominal PosRep (data_name tn))                               rep xt args')
            (InferRefined,PrdRep) -> return (XtorCall (loc, TyData PosRep (Just $ data_name tn) [MkXtorSig xt argTypes])   rep xt args')
            (InferNominal,CnsRep) -> return (XtorCall (loc, TyNominal NegRep (data_name tn))                               rep xt args')
            (InferRefined,CnsRep) -> return (XtorCall (loc, TyCodata NegRep (Just $ data_name tn) [MkXtorSig xt argTypes]) rep xt args')

--
-- Structural pattern and copattern matches:
--
genConstraintsSTerm (XMatch loc rep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      (fvarsPos, fvarsNeg) <- freshTVars (fmap fromMaybeVar <$> scase_args)
                      cmd' <- withContext fvarsPos (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_ext scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  case rep of
        PrdRep -> return $ XMatch (loc, TyCodata PosRep Nothing (snd <$> cases')) rep Structural (fst <$> cases')
        CnsRep -> return $ XMatch (loc, TyData   NegRep Nothing (snd <$> cases')) rep Structural (fst <$> cases')

--
-- Nominal pattern and copattern matches:
--
genConstraintsSTerm (XMatch _ _ Nominal []) =
  -- We know that empty matches cannot be parsed as nominal.
  -- It is therefore save to take the head of the xtors in the other cases.
  throwGenError ["Unreachable: A nominal match needs to have at least one case."]
genConstraintsSTerm (XMatch loc rep Nominal cases@(pmcase:_)) = do
  tn <- lookupDataDecl (scase_name pmcase)
  checkCorrectness (scase_name <$> cases) tn
  checkExhaustiveness (scase_name <$> cases) tn
  im <- asks (inferMode . snd)
  cases' <- forM cases (\MkSCase {..} -> do
                           (fvarsPos, fvarsNeg) <- freshTVars (fmap fromMaybeVar <$> scase_args)
                           cmd' <- withContext fvarsPos (genConstraintsCommand scase_cmd)
                           case im of
                             InferNominal -> do
                               x <- sig_args <$> lookupXtorSig scase_name PosRep
                               genConstraintsSCaseArgs x fvarsNeg loc
                             InferRefined -> do
                               x1 <- sig_args <$> (translateXtorSigLower =<< lookupXtorSig scase_name PosRep)
                               x2 <- sig_args <$> (translateXtorSigUpper =<< lookupXtorSig scase_name NegRep)
                               genConstraintsSCaseArgs x1 fvarsNeg loc -- Empty translation as lower bound
                               genConstraintsSCaseArgs fvarsPos x2 loc -- Full translation as upper bound
                           return (MkSCase scase_ext scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  case (im, rep) of
        (InferNominal,PrdRep) -> return $ XMatch (loc, TyNominal PosRep (data_name tn))                        rep Nominal (fst <$> cases')
        (InferRefined,PrdRep) -> return $ XMatch (loc, TyCodata PosRep (Just $ data_name tn) (snd <$> cases')) rep Nominal (fst <$> cases')
        (InferNominal,CnsRep) -> return $ XMatch (loc, TyNominal NegRep (data_name tn))                        rep Nominal (fst <$> cases')
        (InferRefined,CnsRep) -> return $ XMatch (loc, TyData NegRep (Just $ data_name tn) (snd <$> cases'))   rep Nominal (fst <$> cases')
--
-- Mu and TildeMu abstractions:
--
genConstraintsSTerm (MuAbs loc PrdRep bs cmd) = do
  (fvpos, fvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
  cmd' <- withContext (MkTypArgs [] [fvneg]) (genConstraintsCommand cmd)
  return (MuAbs (loc, fvpos) PrdRep bs cmd')
genConstraintsSTerm (MuAbs loc CnsRep bs cmd) = do
  (fvpos, fvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
  cmd' <- withContext (MkTypArgs [fvpos] []) (genConstraintsCommand cmd)
  return (MuAbs (loc, fvneg) CnsRep bs cmd')
genConstraintsSTerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Structural } t args) = do
  args' <- sequence (genConstraintsSTerm <$> args)
  (retTypePos, retTypeNeg) <- freshTVar (DtorAp loc)
  let codataType = TyCodata NegRep Nothing [MkXtorSig xt (MkTypArgs (getTypeSTerm <$> args') [retTypeNeg])]
  t' <- genConstraintsSTerm t
  addConstraint (SubType (DtorApConstraint loc) (getTypeSTerm t') codataType)
  return (Dtor (loc,retTypePos) xt t' args')
genConstraintsSTerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Nominal } t args) = do
  args' <- sequence (genConstraintsSTerm <$> args)
  tn <- lookupDataDecl xt
  t'<- genConstraintsSTerm t
  im <- asks (inferMode . snd)
  ty <- case im of
    InferNominal -> return $ TyNominal NegRep (data_name tn)
    InferRefined -> translateTypeUpper $ TyNominal NegRep (data_name tn)
  addConstraint (SubType (DtorApConstraint loc) (getTypeSTerm t') ty )
  im <- asks (inferMode . snd)
  xtorSig <- case im of
    InferNominal -> lookupXtorSig xt NegRep
    InferRefined -> translateXtorSigUpper =<< lookupXtorSig xt NegRep
  when (length args' /= length (prdTypes $ sig_args xtorSig)) $
    throwGenError ["Dtor " <> unXtorName xt <> " called with incorrect number of arguments"]
  -- Nominal type constraint!!
  forM_ (zip args' (prdTypes $ sig_args xtorSig)) $ \(t1,t2) -> addConstraint $ SubType (DtorArgsConstraint loc) (getTypeSTerm t1) t2
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
genConstraintsSTerm (Match loc t cases@(MkACase _ xtn@(MkXtorName Nominal _) _ _:_)) = do
  t' <- genConstraintsSTerm t
  tn@NominalDecl{..} <- lookupDataDecl xtn
  checkCorrectness (acase_name <$> cases) tn
  checkExhaustiveness (acase_name <$> cases) tn
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  (cases',casesXtssNeg,casesXtssPos) <- unzip3 <$> sequence (genConstraintsATermCase retTypeNeg <$> cases)
  im <- asks (inferMode . snd)
  -- Nominal type constraint!!
  case im of
    InferNominal -> genConstraintsACaseArgs (data_xtors PosRep) casesXtssNeg loc
    InferRefined -> do
      xtssLower <- mapM translateXtorSigLower $ data_xtors PosRep 
      xtssUpper <- mapM translateXtorSigUpper $ data_xtors NegRep
      genConstraintsACaseArgs xtssLower casesXtssNeg loc -- empty refinement as lower bound
      genConstraintsACaseArgs casesXtssPos xtssUpper loc -- full refinement as upper bound
  let ty = case im of
        InferNominal -> TyNominal NegRep data_name
        InferRefined -> TyData NegRep (Just data_name) casesXtssNeg
  addConstraint (SubType (PatternMatchConstraint loc) (getTypeSTerm t') ty)
  return (Match (loc,retTypePos) t' cases')

genConstraintsSTerm (Match loc t cases) = do
  t' <- genConstraintsSTerm t
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  (cases',casesXtssNeg,_) <- unzip3 <$> sequence (genConstraintsATermCase retTypeNeg <$> cases)
  addConstraint (SubType (PatternMatchConstraint loc) (getTypeSTerm t') (TyData NegRep Nothing casesXtssNeg))
  return (Match (loc, retTypePos) t' cases')

{-
comatch { X_1(x_1,...,x_n) => e_1, ... }

If X_1 has nominal type N, then:
- All X_i must be destructors of type N (correctness)
- All destructors of type N must appear in comatch (exhaustiveness)
- All e_i must have same type, this is the return type
- Types of x_1,...,x_n in e_i must correspond with types in declaration of X_i
-}
genConstraintsSTerm (Comatch loc cocases@(MkACase _ xtn@(MkXtorName Nominal _) _ _:_)) = do
  tn@NominalDecl{..} <- lookupDataDecl xtn
  checkCorrectness (acase_name <$> cocases) tn
  checkExhaustiveness (acase_name <$> cocases) tn
  (cocases',cocasesXtssNeg,cocasesXtssPos) <- unzip3 <$> sequence (genConstraintsATermCocase <$> cocases)
  im <- asks (inferMode . snd)
  -- Nominal type constraint!!
  case im of
    InferNominal -> genConstraintsACaseArgs (data_xtors PosRep) cocasesXtssNeg loc
    InferRefined -> do
      xtssLower <- mapM translateXtorSigLower $ data_xtors PosRep
      xtssUpper <- mapM translateXtorSigUpper $ data_xtors NegRep
      genConstraintsACaseArgs xtssLower cocasesXtssNeg loc -- empty refinement as lower bound
      genConstraintsACaseArgs cocasesXtssPos xtssUpper loc -- full refinement as upper bound
  let ty = case im of
        InferNominal -> TyNominal PosRep data_name
        InferRefined -> TyCodata PosRep (Just data_name) cocasesXtssNeg
  return (Comatch (loc, ty) cocases')

genConstraintsSTerm (Comatch loc cocases) = do
  (cocases',cocasesXtssNeg,_) <- unzip3 <$> sequence (genConstraintsATermCocase <$> cocases)
  let ty = TyCodata PosRep Nothing cocasesXtssNeg
  return (Comatch (loc,ty) cocases')

genConstraintsATermCase :: Typ Neg
                        -> ACase Parsed
                        -> GenM (ACase Inferred, XtorSig Neg, XtorSig Pos)
genConstraintsATermCase retType MkACase { acase_ext, acase_name, acase_args, acase_term } = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (freshTVar . ProgramVariable . fromMaybeVar) -- Generate type var for each case arg
  acase_term' <- withContext (MkTypArgs argtsPos []) (genConstraintsSTerm acase_term) -- Type case term using new type vars
  addConstraint (SubType (CaseConstraint acase_ext) (getTypeSTerm acase_term') retType) -- Case type
  let sigNeg = MkXtorSig acase_name (MkTypArgs argtsNeg [])
  let sigPos = MkXtorSig acase_name (MkTypArgs argtsPos [])
  return (MkACase acase_ext acase_name acase_args acase_term', sigNeg, sigPos)

genConstraintsATermCocase :: ACase Parsed
                          -> GenM (ACase Inferred, XtorSig Neg, XtorSig Pos)
genConstraintsATermCocase MkACase { acase_ext, acase_name, acase_args, acase_term } = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (freshTVar . ProgramVariable . fromMaybeVar)
  acase_term'<- withContext (MkTypArgs argtsPos []) (genConstraintsSTerm acase_term)
  let sigNeg = MkXtorSig acase_name (MkTypArgs argtsNeg [getTypeSTerm acase_term'])
  let sigPos = MkXtorSig acase_name (MkTypArgs argtsPos [])
  return (MkACase acase_ext acase_name acase_args acase_term', sigNeg, sigPos)

genConstraintsACaseArgs :: [XtorSig Pos] -> [XtorSig Neg] -> Loc -> GenM ()
genConstraintsACaseArgs xtsigs1 xtsigs2 loc = do
  forM_ xtsigs1 (\xts1@(MkXtorSig xtn1 _) -> do
    case find (\case (MkXtorSig xtn2 _) -> xtn1==xtn2) xtsigs2 of
      Just xts2 -> do
        let sa1 = sig_args xts1; sa2 = sig_args xts2
        zipWithM_ (\pt1 pt2 -> addConstraint $ SubType (PatternMatchConstraint loc) pt1 pt2) (prdTypes sa1) (prdTypes sa2)
        zipWithM_ (\ct1 ct2 -> addConstraint $ SubType (PatternMatchConstraint loc) ct2 ct1) (cnsTypes sa1) (cnsTypes sa2)
      Nothing -> return ()
    )


genConstraintsCommand :: Command Parsed -> GenM (Command Inferred)
genConstraintsCommand (Done loc) = return (Done loc)
genConstraintsCommand (Print loc t) = do
  t' <- genConstraintsSTerm t
  return (Print loc t')
genConstraintsCommand (Apply loc t1 t2) = do
  t1' <- genConstraintsSTerm t1
  t2' <- genConstraintsSTerm t2
  addConstraint (SubType (CommandConstraint loc) (getTypeSTerm t1') (getTypeSTerm t2'))
  return (Apply loc t1' t2')

genConstraintsSCaseArgs :: TypArgs Pos -> TypArgs Neg -> Loc -> GenM ()
genConstraintsSCaseArgs sa1 sa2 loc = do
  zipWithM_ (\pt1 pt2 -> addConstraint $ SubType (PatternMatchConstraint loc) pt1 pt2) (prdTypes sa1) (prdTypes sa2)
  zipWithM_ (\ct1 ct2 -> addConstraint $ SubType (PatternMatchConstraint loc) ct2 ct1) (cnsTypes sa1) (cnsTypes sa2)

---------------------------------------------------------------------------------------------
-- Symmetric Terms with recursive binding
---------------------------------------------------------------------------------------------

genConstraintsSTermRecursive :: Loc
                             -> FreeVarName
                             -> PrdCnsRep pc -> Term pc Parsed
                             -> GenM (Term pc Inferred)
genConstraintsSTermRecursive loc fv PrdRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  tm <- withSTerm PrdRep fv (FreeVar (loc, x) PrdRep fv) loc (TypeScheme [] x) (genConstraintsSTerm tm)
  addConstraint (SubType RecursionConstraint (getTypeSTerm tm) y)
  return tm
genConstraintsSTermRecursive loc fv CnsRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  tm <- withSTerm CnsRep fv (FreeVar (loc,y) CnsRep fv) loc (TypeScheme [] y) (genConstraintsSTerm tm)
  addConstraint (SubType RecursionConstraint x (getTypeSTerm tm))
  return tm

