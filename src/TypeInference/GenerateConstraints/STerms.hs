module TypeInference.GenerateConstraints.STerms
  ( genConstraintsSTerm
  , genConstraintsSTermRecursive
  , genConstraintsCommand
  ) where

import Control.Monad (forM)

import Pretty.STerms ()
import Pretty.Types ()
import Syntax.STerms
import Syntax.Types
import TypeInference.GenerateConstraints.Definition
import Utils

---------------------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------------------

genConstraintsArgs :: InferenceMode
                   -> XtorArgs Loc FreeVarName
                   -> GenM (XtorArgs () FreeVarName, TypArgs Pos)
genConstraintsArgs im (MkXtorArgs prdArgs cnsArgs) = do
  prdArgs' <- forM prdArgs (genConstraintsSTerm im)
  cnsArgs' <- forM cnsArgs (genConstraintsSTerm im)
  return (MkXtorArgs (fst <$> prdArgs') (fst <$> cnsArgs'), MkTypArgs (snd <$> prdArgs') (snd <$> cnsArgs'))

-- | Generate the constraints for a given STerm.
genConstraintsSTerm :: InferenceMode 
                    -> STerm pc Loc FreeVarName
                    -> GenM ( STerm pc () FreeVarName
                            , Typ (PrdCnsToPol pc))
--
-- Bound variables:
--
-- Bound variables can be looked up in the context.
--
genConstraintsSTerm _ (BoundVar _ rep idx) = do
  ty <- lookupContext rep idx
  return (BoundVar () rep idx, ty)
--
-- Free variables:
--
-- Free variables can be looked up in the environment,
-- where they correspond to typing schemes. This typing
-- scheme has to be instantiated with fresh unification variables.
--
genConstraintsSTerm _ (FreeVar loc PrdRep v) = do
  tys <- lookupPrdEnv v
  ty <- instantiateTypeScheme v loc tys
  return (FreeVar () PrdRep v, ty)
genConstraintsSTerm _ (FreeVar loc CnsRep v) = do
  tys <- lookupCnsEnv v
  ty <- instantiateTypeScheme v loc tys
  return (FreeVar () CnsRep v, ty)
--
-- Constructors and destructors:
--
genConstraintsSTerm im (XtorCall _ PrdRep xt@MkXtorName{ xtorNominalStructural = Structural } args) = do
  (args', argTypes) <- genConstraintsArgs im args
  let resTerm = XtorCall () PrdRep xt args'
  let resType = TyData PosRep [MkXtorSig xt argTypes]
  return (resTerm, resType)
genConstraintsSTerm im (XtorCall _ CnsRep xt@MkXtorName{ xtorNominalStructural = Structural } args) = do
  (args', argTypes) <- genConstraintsArgs im args
  let resTerm = XtorCall () CnsRep xt args'
  let resType = TyCodata NegRep [MkXtorSig xt argTypes]
  return (resTerm, resType)
genConstraintsSTerm im (XtorCall _ rep xt@MkXtorName{ xtorNominalStructural = Nominal } args) = do
  (args', _argTypes) <- genConstraintsArgs im args
  tn <- lookupDataDecl xt
  -- TODO: Check if args of xtor are correct?
  return (XtorCall () rep xt args', TyNominal (foo rep) (data_name tn))
--
-- Structural pattern and copattern matches:
--
genConstraintsSTerm im (XMatch _ PrdRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      (fvarsPos, fvarsNeg) <- freshTVars scase_args
                      cmd' <- withContext fvarsPos (genConstraintsCommand im scase_cmd)
                      return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  let resTerm = XMatch () PrdRep Structural (fst <$> cases')
  let resType = TyCodata PosRep (snd <$> cases')
  return (resTerm, resType)
genConstraintsSTerm im (XMatch _ CnsRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      (fvarsPos, fvarsNeg) <- freshTVars scase_args
                      cmd' <- withContext fvarsPos (genConstraintsCommand im scase_cmd)
                      return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  let resTerm = XMatch () CnsRep Structural (fst <$> cases')
  let resType = TyData NegRep (snd <$> cases')
  return (resTerm, resType)
--
-- Nominal pattern and copattern matches:
--
genConstraintsSTerm _ (XMatch _ _ Nominal []) =
  -- We know that empty matches cannot be parsed as nominal.
  -- It is therefore save to take the head of the xtors in the other cases.
  throwGenError "Unreachable"
genConstraintsSTerm im (XMatch _ PrdRep Nominal cases@(pmcase:_)) = do
  tn <- lookupDataDecl (scase_name pmcase)
  checkExhaustiveness (scase_name <$> cases) tn
  cases' <- forM cases (\MkSCase {..} -> do
                           (x,_) <- lookupCase scase_name
                           cmd' <- withContext x (genConstraintsCommand im scase_cmd)
                           return (MkSCase scase_name scase_args cmd'))
  return (XMatch () PrdRep Nominal cases', TyNominal PosRep (data_name tn))
genConstraintsSTerm im (XMatch _ CnsRep Nominal cases@(pmcase:_)) = do
  tn <- lookupDataDecl (scase_name pmcase)
  checkExhaustiveness (scase_name <$> cases) tn
  cases' <- forM cases (\MkSCase {..} -> do
                           (x,_) <- lookupCase scase_name
                           cmd' <- withContext x (genConstraintsCommand im scase_cmd)
                           return (MkSCase scase_name scase_args cmd'))
  return (XMatch () CnsRep Nominal cases', TyNominal NegRep (data_name tn))
--
-- Mu and TildeMu abstractions:
--
genConstraintsSTerm im (MuAbs _ PrdRep bs cmd) = do
  (fvpos, fvneg) <- freshTVar (ProgramVariable bs)
  cmd' <- withContext (MkTypArgs [] [fvneg]) (genConstraintsCommand im cmd)
  return (MuAbs () PrdRep bs cmd', fvpos)
genConstraintsSTerm im (MuAbs _ CnsRep bs cmd) = do
  (fvpos, fvneg) <- freshTVar (ProgramVariable bs)
  cmd' <- withContext (MkTypArgs [fvpos] []) (genConstraintsCommand im cmd)
  return (MuAbs () CnsRep bs cmd', fvneg)

genConstraintsCommand :: InferenceMode -> Command Loc FreeVarName -> GenM (Command () FreeVarName)
genConstraintsCommand _  (Done _) = return (Done ())
genConstraintsCommand im (Print _ t) = do
  (t',_) <- genConstraintsSTerm im t
  return (Print () t')
genConstraintsCommand im (Apply loc t1 t2) = do
  (t1',ty1) <- genConstraintsSTerm im t1
  (t2',ty2) <- genConstraintsSTerm im t2
  addConstraint (SubType (CommandConstraint loc) ty1 ty2)
  return (Apply () t1' t2')


---------------------------------------------------------------------------------------------
-- Symmetric Terms with recursive binding
---------------------------------------------------------------------------------------------

genConstraintsSTermRecursive :: FreeVarName -> InferenceMode
                             -> PrdCnsRep pc -> STerm pc Loc FreeVarName
                             -> GenM (STerm pc () FreeVarName, Typ (PrdCnsToPol pc))
genConstraintsSTermRecursive fv im PrdRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  (tm, ty) <- withPrdEnv fv (FreeVar () PrdRep fv) (TypeScheme [] x) (genConstraintsSTerm im tm)
  addConstraint (SubType RecursionConstraint ty y)
  return (tm, ty)
genConstraintsSTermRecursive fv im CnsRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  (tm, ty) <- withCnsEnv fv (FreeVar () CnsRep fv) (TypeScheme [] y) (genConstraintsSTerm im tm)
  addConstraint (SubType RecursionConstraint x ty)
  return (tm, ty)

