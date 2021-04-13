module TypeInference.GenerateConstraints.STerms
  ( genConstraintsSTerm
  , genConstraintsSTermRecursive
  , genConstraintsCommand
  ) where

import Control.Monad.Reader
import qualified Data.Map as M


import Pretty.Pretty (ppPrint)
import Pretty.STerms ()
import Pretty.Types ()
import Syntax.STerms
import Syntax.Program hiding (lookupXtor)
import Syntax.Types
import TypeInference.GenerateConstraints.Definition
import Utils

---------------------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------------------

-- | Checks for a given list of XtorNames and a type declaration whether:
-- (1) All the xtornames occur in the type declaration. (Correctness)
-- (2) All xtors of the type declaration are matched against. (Exhaustiveness)
checkExhaustiveness :: [XtorName] -- ^ The xtor names used in the pattern match
                    -> DataDecl   -- ^ The type declaration to check against.
                    -> GenM ()
checkExhaustiveness matched decl = do
  let declared = sig_name <$> (data_xtors decl)
  forM_ matched $ \xn -> when (not (xn `elem` declared)) (throwGenError ("Pattern Match Error. The xtor " ++ ppPrint xn ++ " does not occur in the declaration of type " ++ ppPrint (data_name decl)))
  forM_ declared $ \xn -> when (not (xn `elem` matched)) (throwGenError ("Pattern Match Exhaustiveness Error. Xtor: " ++ ppPrint xn ++ " of type " ++ ppPrint (data_name decl) ++ " is not matched against." ))

genConstraintsArgs :: XtorArgs Loc FreeVarName -> GenM (XtorArgs () FreeVarName, TypArgs Pos)
genConstraintsArgs (MkXtorArgs prdArgs cnsArgs) = do
  prdArgs' <- forM prdArgs genConstraintsSTerm
  cnsArgs' <- forM cnsArgs genConstraintsSTerm
  return (MkXtorArgs (fst <$> prdArgs') (fst <$> cnsArgs'), MkTypArgs (snd <$> prdArgs') (snd <$> cnsArgs'))

genConstraintsSTerm :: STerm pc Loc FreeVarName -> GenM (STerm pc () FreeVarName, Typ (PrdCnsToPol pc))
genConstraintsSTerm (BoundVar _ rep idx) = do
  ty <- lookupType rep idx
  return (BoundVar () rep idx, ty)
genConstraintsSTerm (FreeVar loc PrdRep v) = do
  prdEnv <- asks (prdEnv . env)
  case M.lookup v prdEnv of
    Just (_,tys) -> do
      ty <- instantiateTypeScheme v loc tys
      return (FreeVar () PrdRep v, ty)
    Nothing -> throwGenError $ "Unbound free producer variable in STerm: " ++ ppPrint v
genConstraintsSTerm (FreeVar loc CnsRep v) = do
  cnsEnv <- asks (cnsEnv . env)
  case M.lookup v cnsEnv of
    Just (_,tys) -> do
      ty <- instantiateTypeScheme v loc tys
      return (FreeVar () CnsRep v, ty)
    Nothing -> throwGenError $ "Unbound free consumer variable in STerm: " ++ ppPrint v
genConstraintsSTerm (XtorCall _ PrdRep xt@(MkXtorName { xtorNominalStructural = Structural }) args) = do
  (args', argTypes) <- genConstraintsArgs args
  return (XtorCall () PrdRep xt args', TyData PosRep [MkXtorSig xt argTypes])
genConstraintsSTerm (XtorCall _ CnsRep xt@(MkXtorName { xtorNominalStructural = Structural }) args) = do
  (args', argTypes) <- genConstraintsArgs args
  return (XtorCall () CnsRep xt args', TyCodata NegRep [MkXtorSig xt argTypes])
genConstraintsSTerm (XtorCall _ rep xt@(MkXtorName { xtorNominalStructural = Nominal }) args) = do
  (args', _argTypes) <- genConstraintsArgs args
  tn <- lookupXtor xt
  -- TODO: Check if args of xtor are correct?
  return (XtorCall () rep xt args', TyNominal (foo rep) (data_name tn))
genConstraintsSTerm (XMatch _ PrdRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      (fvarsPos, fvarsNeg) <- freshTVars scase_args
                      cmd' <- withContext fvarsPos (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  return (XMatch () PrdRep Structural (fst <$> cases'), TyCodata PosRep (snd <$> cases'))
genConstraintsSTerm (XMatch _ CnsRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      (fvarsPos, fvarsNeg) <- freshTVars scase_args
                      cmd' <- withContext fvarsPos (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  return (XMatch () CnsRep Structural (fst <$> cases'), TyData NegRep (snd <$> cases'))
-- We know that empty matches cannot be parsed as nominal, so it is save to take the head of the xtors.
genConstraintsSTerm (XMatch _ _ Nominal []) =
  throwGenError "Unreachable: A Match on a nominal type with 0 cases cannot be parsed."
genConstraintsSTerm (XMatch _ PrdRep Nominal cases@(pmcase:_)) = do
  tn <- lookupXtor (scase_name pmcase)
  checkExhaustiveness (scase_name <$> cases) tn
  cases' <- forM cases (\MkSCase {..} -> do
                           (x,_) <- lookupCase scase_name
                           cmd' <- withContext x (genConstraintsCommand scase_cmd)
                           return (MkSCase scase_name scase_args cmd'))
  return (XMatch () PrdRep Nominal cases', TyNominal PosRep (data_name tn))
genConstraintsSTerm (XMatch _ CnsRep Nominal cases@(pmcase:_)) = do
  tn <- lookupXtor (scase_name pmcase)
  checkExhaustiveness (scase_name <$> cases) tn
  cases' <- forM cases (\MkSCase {..} -> do
                           (x,_) <- lookupCase scase_name
                           cmd' <- withContext x (genConstraintsCommand scase_cmd)
                           return (MkSCase scase_name undefined cmd'))
  return (XMatch () CnsRep Nominal cases', TyNominal NegRep (data_name tn))
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

genConstraintsSTermRecursive :: FreeVarName -> PrdCnsRep pc -> STerm pc Loc FreeVarName -> GenM (STerm pc () FreeVarName, Typ (PrdCnsToPol pc))
genConstraintsSTermRecursive fv PrdRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  let modifyEnv (GenerateReader ctx env@Environment { prdEnv }) = GenerateReader ctx env { prdEnv = M.insert fv (FreeVar () PrdRep fv, TypeScheme [] x) prdEnv }
  (tm, ty) <- local modifyEnv (genConstraintsSTerm tm)
  addConstraint (SubType RecursionConstraint ty y)
  return (tm, ty)
genConstraintsSTermRecursive fv CnsRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  let modifyEnv (GenerateReader ctx env@Environment { cnsEnv }) = GenerateReader ctx env { cnsEnv = M.insert fv (FreeVar () CnsRep fv, TypeScheme [] y) cnsEnv }
  (tm, ty) <- local modifyEnv (genConstraintsSTerm tm)
  addConstraint (SubType RecursionConstraint x ty)
  return (tm, ty)

