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

genConstraintsArgs :: XtorArgs Loc
                   -> GenM (XtorArgs (), TypArgs Pos)
genConstraintsArgs (MkXtorArgs prdArgs cnsArgs) = do
  prdArgs' <- forM prdArgs genConstraintsSTerm
  cnsArgs' <- forM cnsArgs genConstraintsSTerm
  return (MkXtorArgs (fst <$> prdArgs') (fst <$> cnsArgs'), MkTypArgs (snd <$> prdArgs') (snd <$> cnsArgs'))

-- | Generate the constraints for a given STerm.
genConstraintsSTerm :: STerm pc Loc
                    -> GenM ( STerm pc ()
                            , Typ (PrdCnsToPol pc))
--
-- Bound variables:
--
-- Bound variables can be looked up in the context.
--
genConstraintsSTerm (BoundVar _ rep idx) = do
  ty <- lookupContext rep idx
  return (BoundVar () rep idx, ty)
--
-- Free variables:
--
-- Free variables can be looked up in the environment,
-- where they correspond to typing schemes. This typing
-- scheme has to be instantiated with fresh unification variables.
--
genConstraintsSTerm (FreeVar loc rep v) = do
  tys <- snd <$> lookupSTerm rep v
  ty <- instantiateTypeScheme v loc tys
  return (FreeVar () rep v, ty)
--
-- Xtors
--
genConstraintsSTerm (XtorCall loc rep xt args) = do
  (args', argTypes) <- genConstraintsArgs args
  let resTerm = XtorCall () rep xt args'
  case xtorNominalStructural xt of
    Structural -> do
      let resType = case rep of
            PrdRep -> TyData PosRep [MkXtorSig xt argTypes]
            CnsRep -> TyCodata NegRep [MkXtorSig xt argTypes]
      return (resTerm, resType)
    Nominal -> do
      tn <- lookupDataDecl xt
      -- Check if args of xtor are correct
      xtorSig <- lookupXtorSig xt NegRep
      forM_ (zip (prdTypes argTypes) (prdTypes $ sig_args xtorSig)) $ \(t1,t2) -> do
        addConstraint $ SubType (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc }) t1 t2
      im <- asks (inferMode . snd)
      let resType = case (im, rep) of
            (InferNominal,PrdRep) -> TyNominal PosRep (data_name tn)
            (InferRefined,PrdRep) -> TyData PosRep $ xtorSigMakeStructural <$> [MkXtorSig xt argTypes]
            (InferNominal,CnsRep) -> TyNominal NegRep (data_name tn)
            (InferRefined,CnsRep) -> TyCodata NegRep $ xtorSigMakeStructural <$> [MkXtorSig xt argTypes]
      return (resTerm, resType)
--
-- Structural pattern and copattern matches:
--
genConstraintsSTerm (XMatch _ rep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      (fvarsPos, fvarsNeg) <- freshTVars (fmap fromMaybeVar <$> scase_args)
                      cmd' <- withContext fvarsPos (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  let resTerm = XMatch () rep Structural (fst <$> cases')
  let resType = case rep of
        PrdRep -> TyCodata PosRep (snd <$> cases')
        CnsRep -> TyData NegRep (snd <$> cases')
  return (resTerm, resType)
--
-- Nominal pattern and copattern matches:
--
genConstraintsSTerm (XMatch _ _ Nominal []) =
  -- We know that empty matches cannot be parsed as nominal.
  -- It is therefore save to take the head of the xtors in the other cases.
  throwGenError ["Unreachable: A nominal match needs to have at least one case."]
genConstraintsSTerm (XMatch _ rep Nominal cases@(pmcase:_)) = do
  tn <- lookupDataDecl (scase_name pmcase)
  checkCorrectness (scase_name <$> cases) tn
  checkExhaustiveness (scase_name <$> cases) tn
  cases' <- forM cases (\MkSCase {..} -> do
                           x <- sig_args <$> lookupXtorSig scase_name PosRep
                           (_,fvarsNeg) <- freshTVars (fmap fromMaybeVar <$> scase_args)
                           cmd' <- withContext x (genConstraintsCommand scase_cmd)
                           return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  let resTerm = XMatch () rep Nominal (fst <$> cases')
  im <- asks (inferMode . snd)
  let resType = case (im, rep) of
        (InferNominal,PrdRep) -> TyNominal PosRep (data_name tn)
        (InferRefined,PrdRep) -> TyCodata PosRep (xtorSigMakeStructural . snd <$> cases')
        (InferNominal,CnsRep) -> TyNominal NegRep (data_name tn)
        (InferRefined,CnsRep) -> TyData NegRep (xtorSigMakeStructural . snd <$> cases')
  return (resTerm, resType)
--
-- Mu and TildeMu abstractions:
--
genConstraintsSTerm (MuAbs _ PrdRep bs cmd) = do
  (fvpos, fvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
  cmd' <- withContext (MkTypArgs [] [fvneg]) (genConstraintsCommand cmd)
  return (MuAbs () PrdRep bs cmd', fvpos)
genConstraintsSTerm (MuAbs _ CnsRep bs cmd) = do
  (fvpos, fvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
  cmd' <- withContext (MkTypArgs [fvpos] []) (genConstraintsCommand cmd)
  return (MuAbs () CnsRep bs cmd', fvneg)

genConstraintsCommand :: Command Loc -> GenM (Command ())
genConstraintsCommand (Done _) = return (Done ())
genConstraintsCommand (Print _ t) = do
  (t',_) <- genConstraintsSTerm t
  return (Print () t')
genConstraintsCommand (Apply loc t1 t2) = do
  (t1',ty1) <- genConstraintsSTerm t1
  (t2',ty2) <- genConstraintsSTerm t2
  addConstraint (SubType (CommandConstraint loc) ty1 ty2)
  return (Apply () t1' t2')


---------------------------------------------------------------------------------------------
-- Symmetric Terms with recursive binding
---------------------------------------------------------------------------------------------

genConstraintsSTermRecursive :: Loc
                             -> FreeVarName
                             -> PrdCnsRep pc -> STerm pc Loc
                             -> GenM (STerm pc (), Typ (PrdCnsToPol pc))
genConstraintsSTermRecursive loc fv PrdRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  (tm, ty) <- withSTerm PrdRep fv (FreeVar () PrdRep fv) loc (TypeScheme [] x) (genConstraintsSTerm tm)
  addConstraint (SubType RecursionConstraint ty y)
  return (tm, ty)
genConstraintsSTermRecursive loc fv CnsRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  (tm, ty) <- withSTerm CnsRep fv (FreeVar () CnsRep fv) loc (TypeScheme [] y) (genConstraintsSTerm tm)
  addConstraint (SubType RecursionConstraint x ty)
  return (tm, ty)

