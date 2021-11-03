module TypeInference.GenerateConstraints.STerms
  ( genConstraintsSTerm
  , genConstraintsSTermRecursive
  , genConstraintsCommand
  ) where

import Control.Monad.Reader

import Pretty.STerms ()
import Pretty.Types ()
import Syntax.STerms
import Syntax.Types
import TypeInference.GenerateConstraints.Definition
import Utils
import Lookup

---------------------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------------------

genConstraintsArgs :: XtorArgs Parsed
                   -> GenM (XtorArgs Inferred)
genConstraintsArgs (MkXtorArgs prdArgs cnsArgs) = do
  prdArgs' <- forM prdArgs genConstraintsSTerm
  cnsArgs' <- forM cnsArgs genConstraintsSTerm
  return (MkXtorArgs prdArgs' cnsArgs')

-- | Generate the constraints for a given STerm.
genConstraintsSTerm :: STerm pc Parsed
                    -> GenM ( STerm pc Inferred )
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
        InferRefined -> translateXtorSig =<< lookupXtorSig xt NegRep
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
                      return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
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
                           x <- case im of
                             InferNominal -> sig_args <$> lookupXtorSig scase_name PosRep
                             InferRefined -> sig_args <$> (translateXtorSig =<< lookupXtorSig scase_name PosRep)
                           (_,fvarsNeg) <- freshTVars (fmap fromMaybeVar <$> scase_args)
                           cmd' <- withContext x (genConstraintsCommand scase_cmd)
                           return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
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


---------------------------------------------------------------------------------------------
-- Symmetric Terms with recursive binding
---------------------------------------------------------------------------------------------

genConstraintsSTermRecursive :: Loc
                             -> FreeVarName
                             -> PrdCnsRep pc -> STerm pc Parsed
                             -> GenM (STerm pc Inferred)
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

