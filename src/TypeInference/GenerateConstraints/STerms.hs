module TypeInference.GenerateConstraints.STerms where

import Control.Monad.Reader
import Control.Monad.Except
import qualified Data.Map as M


import Pretty.Pretty
import Syntax.STerms
import Syntax.Program (Environment)
import qualified Syntax.Program as P
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
  forM_ matched $ \xn -> when (not (xn `elem` declared)) (throwError $ GenConstraintsError ("Pattern Match Error. The xtor " ++ ppPrint xn ++ " does not occur in the declaration of type " ++ ppPrint (data_name decl)))
  forM_ declared $ \xn -> when (not (xn `elem` matched)) (throwError $ GenConstraintsError ("Pattern Match Exhaustiveness Error. Xtor: " ++ ppPrint xn ++ " of type " ++ ppPrint (data_name decl) ++ " is not matched against." ))

genConstraintsArgs :: XtorArgs () -> GenM (XtorArgs (), TypArgs Pos)
genConstraintsArgs (MkXtorArgs prdArgs cnsArgs) = do
  prdArgs' <- forM prdArgs genConstraintsSTerm
  cnsArgs' <- forM cnsArgs genConstraintsSTerm
  return (MkXtorArgs (fst <$> prdArgs') (fst <$> cnsArgs'), MkTypArgs (snd <$> prdArgs') (snd <$> cnsArgs'))

genConstraintsSTerm :: STerm pc () -> GenM (STerm pc (), Typ (PrdCnsToPol pc))
genConstraintsSTerm (BoundVar rep idx) = do
  ty <- lookupType rep idx
  return (BoundVar rep idx, ty)
-- The following code for free variables is a temporary hack. Free variables which are bound in the environment are
-- typechecked by substituting the bound term in place of the free variable. This only works because the examples use
-- a fixpoint combinator instead of explicit recursion. Otherwise generation of constraints would not terminate.
-- This will be implemented properly in a future PR.
genConstraintsSTerm (FreeVar PrdRep v _) = do
  prdEnv <- asks (P.prdEnv . env)
  case M.lookup v prdEnv of
    Just (prd,_) -> genConstraintsSTerm prd -- TODO, replace with rhs.
    Nothing -> throwError $ GenConstraintsError $ "Unbound free producer variable in STerm: " ++ ppPrint v
genConstraintsSTerm (FreeVar CnsRep v _) = do
  cnsEnv <- asks (P.cnsEnv . env)
  case M.lookup v cnsEnv of
    Just (cns,_) -> genConstraintsSTerm cns -- TODO, replace with rhs.
    Nothing -> throwError $ GenConstraintsError $ "Unbound free consumer variable in STerm: " ++ ppPrint v
genConstraintsSTerm (XtorCall PrdRep xt@(MkXtorName { xtorNominalStructural = Structural }) args) = do
  (args', argTypes) <- genConstraintsArgs args
  return (XtorCall PrdRep xt args', TyStructural PosRep DataRep [MkXtorSig xt argTypes])
genConstraintsSTerm (XtorCall CnsRep xt@(MkXtorName { xtorNominalStructural = Structural }) args) = do
  (args', argTypes) <- genConstraintsArgs args
  return (XtorCall CnsRep xt args', TyStructural NegRep CodataRep [MkXtorSig xt argTypes])
genConstraintsSTerm (XtorCall rep xt@(MkXtorName { xtorNominalStructural = Nominal }) args) = do
  (args', _argTypes) <- genConstraintsArgs args
  tn <- lookupXtor xt
  -- TODO: Check if args of xtor are correct?
  return (XtorCall rep xt args', TyNominal (foo rep) (data_name tn))
genConstraintsSTerm (XMatch PrdRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      (fvarsPos, fvarsNeg) <- freshTVars scase_args
                      cmd' <- local (\gr@GenerateReader{..} -> gr { context = fvarsPos:context }) (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  return (XMatch PrdRep Structural (fst <$> cases'), TyStructural PosRep CodataRep (snd <$> cases'))
genConstraintsSTerm (XMatch CnsRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      (fvarsPos, fvarsNeg) <- freshTVars scase_args
                      cmd' <- local (\gr@GenerateReader{..} -> gr { context = fvarsPos:context }) (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  return (XMatch CnsRep Structural (fst <$> cases'), TyStructural NegRep DataRep (snd <$> cases'))
-- We know that empty matches cannot be parsed as nominal, so it is save to take the head of the xtors.
genConstraintsSTerm (XMatch _ Nominal []) = throwError $ GenConstraintsError "Unreachable: A Match on a nominal type with 0 cases cannot be parsed."
genConstraintsSTerm (XMatch PrdRep Nominal cases@(pmcase:_)) = do
  tn <- lookupXtor (scase_name pmcase)
  checkExhaustiveness (scase_name <$> cases) tn
  cases' <- forM cases (\MkSCase {..} -> do
                           (x,_) <- lookupCase scase_name
                           cmd' <- local (\gr@GenerateReader{..} -> gr { context = x:context }) (genConstraintsCommand scase_cmd)
                           return (MkSCase scase_name scase_args cmd'))
  return (XMatch PrdRep Nominal cases', TyNominal PosRep (data_name tn))
genConstraintsSTerm (XMatch CnsRep Nominal cases@(pmcase:_)) = do
  tn <- lookupXtor (scase_name pmcase)
  checkExhaustiveness (scase_name <$> cases) tn
  cases' <- forM cases (\MkSCase {..} -> do
                           (x,_) <- lookupCase scase_name
                           cmd' <- local (\gr@GenerateReader{..} -> gr { context = x:context }) (genConstraintsCommand scase_cmd)
                           return (MkSCase scase_name undefined cmd'))
  return (XMatch CnsRep Nominal cases', TyNominal NegRep (data_name tn))
genConstraintsSTerm (MuAbs PrdRep () cmd) = do
  (fvpos, fvneg) <- freshTVar
  cmd' <- local (\gr@GenerateReader{..} -> gr { context = (MkTypArgs [] [fvneg]):context }) (genConstraintsCommand cmd)
  return (MuAbs PrdRep () cmd', fvpos)
genConstraintsSTerm (MuAbs CnsRep () cmd) = do
  (fvpos, fvneg) <- freshTVar
  cmd' <- local (\gr@GenerateReader{..} -> gr { context = (MkTypArgs [fvpos] []):context }) (genConstraintsCommand cmd)
  return (MuAbs CnsRep () cmd', fvneg)

genConstraintsCommand :: Command () -> GenM (Command ())
genConstraintsCommand Done = return Done
genConstraintsCommand (Print t) = do
  (t',_) <- genConstraintsSTerm t
  return (Print t')
genConstraintsCommand (Apply t1 t2) = do
  (t1',ty1) <- genConstraintsSTerm t1
  (t2',ty2) <- genConstraintsSTerm t2
  addConstraint (SubType ty1 ty2)
  return (Apply t1' t2')

sgenerateConstraints :: STerm pc ()
                      -> Environment
                      -> Either Error ((STerm pc (), Typ (PrdCnsToPol pc)), ConstraintSet)
sgenerateConstraints tm env = runGenM env (genConstraintsSTerm tm)

sgenerateConstraintsCmd :: Command () -> Environment -> Either Error ConstraintSet
sgenerateConstraintsCmd cmd env = snd <$> runGenM env (genConstraintsCommand cmd)
