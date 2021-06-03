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

---------------------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------------------

genConstraintsArgs :: XtorArgs Loc FreeVarName
                   -> GenM (XtorArgs () FreeVarName, TypArgs (PrdCnsToPol Prd))
genConstraintsArgs (MkXtorArgs prdArgs cnsArgs) = do
  prdArgs' <- forM prdArgs genConstraintsSTerm
  cnsArgs' <- forM cnsArgs genConstraintsSTerm
  return (MkXtorArgs (fst <$> prdArgs') (fst <$> cnsArgs'), MkTypArgs (snd <$> prdArgs') (snd <$> cnsArgs'))

-- | Generate the constraints for a given STerm.
genConstraintsSTerm :: STerm pc Loc FreeVarName
                    -> GenM ( STerm pc () FreeVarName
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
genConstraintsSTerm (FreeVar loc PrdRep v) = do
  tys <- lookupPrdEnv v
  ty <- instantiateTypeScheme v loc tys
  return (FreeVar () PrdRep v, ty)
genConstraintsSTerm (FreeVar loc CnsRep v) = do
  tys <- lookupCnsEnv v
  ty <- instantiateTypeScheme v loc tys
  return (FreeVar () CnsRep v, ty)
--
-- Constructors and destructors:
--
genConstraintsSTerm (XtorCall _ PrdRep xt@MkXtorName{ xtorNominalStructural = Structural } args) = do
  (args', argTypes) <- genConstraintsArgs args
  let resTerm = XtorCall () PrdRep xt args'
  let resType = TyData PosRep [MkXtorSig xt argTypes]
  return (resTerm, resType)
genConstraintsSTerm (XtorCall _ CnsRep xt@MkXtorName{ xtorNominalStructural = Structural } args) = do
  (args', argTypes) <- genConstraintsArgs args
  let resTerm = XtorCall () CnsRep xt args'
  let resType = TyCodata NegRep [MkXtorSig xt argTypes]
  return (resTerm, resType)

genConstraintsSTerm (XtorCall loc PrdRep xt@MkXtorName{ xtorNominalStructural = Nominal } args) = do
  (args', argTypes) <- genConstraintsArgs args
  tn <- lookupDataDecl xt
  -- Check if args of xtor are correct
  xtorSig <- lookupXtorSig tn xt NegRep
  forM_ (zip (prdTypes argTypes) (prdTypes $ sig_args xtorSig)) $ \(t1,t2) -> addConstraint $ SubType (CtorArgsConstraint loc) t1 t2
  im <- asks inferMode
  let ty = case im of
        InferNominal -> TyNominal PosRep (data_name tn)
        InferRefined -> TyRefined PosRep (data_name tn) $ TyData PosRep [MkXtorSig xt argTypes]
  return (XtorCall () PrdRep xt args', ty)
genConstraintsSTerm (XtorCall loc CnsRep xt@MkXtorName{ xtorNominalStructural = Nominal } args) = do
  (args', argTypes) <- genConstraintsArgs args
  tn <- lookupDataDecl xt
  -- Check if args of xtor are correct
  xtorSig <- lookupXtorSig tn xt NegRep
  forM_ (zip (prdTypes argTypes) (prdTypes $ sig_args xtorSig)) $ \(t1,t2) -> addConstraint $ SubType (DtorArgsConstraint loc) t1 t2
  im <- asks inferMode
  let ty = case im of
        InferNominal -> TyNominal NegRep (data_name tn)
        InferRefined -> TyRefined NegRep (data_name tn) $ TyCodata NegRep [MkXtorSig xt argTypes]
  return (XtorCall () CnsRep xt args', ty)
--
-- Structural pattern and copattern matches:
--
genConstraintsSTerm (XMatch _ PrdRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      (fvarsPos, fvarsNeg) <- freshTVars scase_args
                      cmd' <- withContext fvarsPos (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  let resTerm = XMatch () PrdRep Structural (fst <$> cases')
  let resType = TyCodata PosRep (snd <$> cases')
  return (resTerm, resType)
genConstraintsSTerm (XMatch _ CnsRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      (fvarsPos, fvarsNeg) <- freshTVars scase_args
                      cmd' <- withContext fvarsPos (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  let resTerm = XMatch () CnsRep Structural (fst <$> cases')
  let resType = TyData NegRep (snd <$> cases')
  return (resTerm, resType)
--
-- Nominal pattern and copattern matches:
--
genConstraintsSTerm (XMatch _ _ Nominal []) =
  -- We know that empty matches cannot be parsed as nominal.
  -- It is therefore save to take the head of the xtors in the other cases.
  throwGenError "Unreachable"
genConstraintsSTerm (XMatch _ PrdRep Nominal cases@(pmcase:_)) = do
  tn <- lookupDataDecl (scase_name pmcase)
  checkExhaustiveness (scase_name <$> cases) tn
  cases' <- forM cases (\MkSCase {..} -> do
                           (x,_) <- lookupCase scase_name
                           (_,fvarsNeg) <- freshTVars scase_args
                           cmd' <- withContext x (genConstraintsCommand scase_cmd)
                           return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  im <- asks inferMode
  let ty = case im of
        InferNominal -> TyNominal PosRep (data_name tn)
        InferRefined -> TyRefined PosRep (data_name tn) $ TyCodata PosRep (snd <$> cases')
  return (XMatch () PrdRep Nominal (fst <$> cases'), ty)
genConstraintsSTerm (XMatch _ CnsRep Nominal cases@(pmcase:_)) = do
  tn <- lookupDataDecl (scase_name pmcase)
  checkExhaustiveness (scase_name <$> cases) tn
  cases' <- forM cases (\MkSCase {..} -> do
                           (x,_) <- lookupCase scase_name
                           (_,fvarsNeg) <- freshTVars scase_args
                           cmd' <- withContext x (genConstraintsCommand scase_cmd)
                           return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  im <- asks inferMode
  let ty = case im of
        InferNominal -> TyNominal NegRep (data_name tn)
        InferRefined -> TyRefined NegRep (data_name tn) $ TyData NegRep (snd <$> cases')
  return (XMatch () CnsRep Nominal (fst <$> cases'), ty)
--
-- Mu and TildeMu abstractions:
--
genConstraintsSTerm (MuAbs _ PrdRep bs cmd) = do
  (fvpos, fvneg) <- freshTVar (ProgramVariable bs)
  cmd' <- withContext (MkTypArgs [] [fvneg]) (genConstraintsCommand cmd)
  return (MuAbs () PrdRep bs cmd', fvpos)
genConstraintsSTerm (MuAbs _ CnsRep bs cmd) = do
  (fvpos, fvneg) <- freshTVar (ProgramVariable bs)
  cmd' <- withContext (MkTypArgs [fvpos] []) (genConstraintsCommand cmd)
  return (MuAbs () CnsRep bs cmd', fvneg)

genConstraintsCommand :: Command Loc FreeVarName -> GenM (Command () FreeVarName)
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

genConstraintsSTermRecursive :: FreeVarName
                             -> PrdCnsRep pc -> STerm pc Loc FreeVarName
                             -> GenM (STerm pc () FreeVarName, Typ (PrdCnsToPol pc))
genConstraintsSTermRecursive fv PrdRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  (tm, ty) <- withPrdEnv fv (FreeVar () PrdRep fv) (TypeScheme [] x) (genConstraintsSTerm tm)
  addConstraint (SubType RecursionConstraint ty y)
  return (tm, ty)
genConstraintsSTermRecursive fv CnsRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  (tm, ty) <- withCnsEnv fv (FreeVar () CnsRep fv) (TypeScheme [] y) (genConstraintsSTerm tm)
  addConstraint (SubType RecursionConstraint x ty)
  return (tm, ty)

