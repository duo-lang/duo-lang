module GenerateConstraints
  ( generateConstraints
  , typedTermToType
  ) where

import qualified Data.Map as M
import Control.Monad.State
import Control.Monad.Except

import Pretty
import Syntax.Terms
import Syntax.Types
import Syntax.Program
import Utils
import Eval.Substitution

{-
Constraint generation is split in two phases:

  1) The term is annotated with fresh unification variables
  2) The term is traversed and constraints are collected

This seperation is only possible because in our system, there is a 1-to-1 correspondence between program variables
and unifcation variables. Thus, during the actual constraint generation, we don't ever have to come up with new
unifcation variables.
-}

-------------------------------------------------------------------------------------
-- Phase 1: Term annotation
-------------------------------------------------------------------------------------

data GenerateState = GenerateState { varGen :: Int, envGen :: Environment }
type GenerateM a = StateT GenerateState (Except Error) a

lookupCase :: XtorName -> GenerateM (Twice [SimpleType], XtorArgs SimpleType)
lookupCase xt = do
  env <- gets envGen
  case M.lookup xt (envToXtorMap env) of
    Nothing -> throwError $ GenConstraintsError ("GenerateConstraints: The xtor " ++ ppPrint xt ++ " could not be looked up.")
    Just types@(Twice prdTypes cnsTypes) -> do
      let prds = (\ty -> FreeVar PrdRep "y" ty) <$> prdTypes
      let cnss = (\ty -> FreeVar CnsRep "y" ty) <$> cnsTypes
      return (types, MkXtorArgs prds cnss)


freshVars :: Int -> PrdCnsRep pc -> GenerateM [(SimpleType, Term pc SimpleType)]
freshVars k pc = do
  n <- gets varGen
  modify (\gs@GenerateState { varGen } -> gs {varGen = varGen + k })
  return [(uv, FreeVar pc ("x" ++ show i) uv) | i <- [n..n+k-1], let uv = TyUVar () (MkUVar i)]

annotateCase :: Case () -> GenerateM (Case SimpleType)
-- In Matches on Structural types, all arguments to xtors have to be annotated by a unification variable, since
-- we don't know their type yet.
annotateCase (MkCase xt@(MkXtorName { xtorNominalStructural = Structural }) (Twice prds cnss) cmd) = do
  (prdUVars, prdTerms) <- unzip <$> freshVars (length prds) PrdRep
  (cnsUVars, cnsTerms) <- unzip <$> freshVars (length cnss) CnsRep
  cmd' <- annotateCommand cmd
  return (MkCase xt (Twice prdUVars cnsUVars) (commandOpening (MkXtorArgs prdTerms cnsTerms) cmd'))
-- In Matches on nominal types we don't add unification variables, since types of arguments are known from type declaration.
annotateCase (MkCase xt@(MkXtorName { xtorNominalStructural = Nominal }) _caseArgs cmd) = do
  cmd' <- annotateCommand cmd
  (vars, args) <- lookupCase xt
  return (MkCase xt vars (commandOpening args cmd'))

annotateTerm :: Term pc () -> GenerateM (Term pc SimpleType)
annotateTerm (FreeVar _ v _)     = throwError $ GenConstraintsError ("Unknown free variable: \"" ++ v ++ "\"")
annotateTerm (BoundVar idx pc) = return (BoundVar idx pc)
annotateTerm (XtorCall s xt (MkXtorArgs prdArgs cnsArgs)) = do
  prdArgs' <- mapM annotateTerm prdArgs
  cnsArgs' <- mapM annotateTerm cnsArgs
  return (XtorCall s xt (MkXtorArgs prdArgs' cnsArgs'))
annotateTerm (Match pc sn cases) = do
  cases' <- forM cases annotateCase
  return (Match pc sn cases')
annotateTerm (MuAbs PrdRep _ cmd) = do
  (uv, freeVar) <- head <$> freshVars 1 CnsRep
  cmd' <- annotateCommand cmd
  return (MuAbs PrdRep uv (commandOpeningSingle CnsRep freeVar cmd'))
annotateTerm (MuAbs CnsRep _ cmd) = do
  (uv, freeVar) <- head <$> freshVars 1 PrdRep
  cmd' <- annotateCommand cmd
  return (MuAbs CnsRep uv (commandOpeningSingle PrdRep freeVar cmd'))

annotateCommand :: Command () -> GenerateM (Command SimpleType)
annotateCommand Done = return Done
annotateCommand (Print t) = Print <$> (annotateTerm t)
annotateCommand (Apply t1 t2) = do
  t1' <- annotateTerm t1
  t2' <- annotateTerm t2
  return (Apply t1' t2')

---------------------------------------------------------------------------------------------
-- Phase 2: Constraint collection
---------------------------------------------------------------------------------------------

argsToTypes :: Environment -> XtorArgs SimpleType -> Either Error (Twice [SimpleType])
argsToTypes env (MkXtorArgs prdargs cnsargs) = do
  prdArgs' <- sequence (typedTermToType env <$> prdargs)
  cnsArgs' <- sequence (typedTermToType env <$> cnsargs)
  return (Twice prdArgs' cnsArgs')

getCaseType :: Case a -> XtorSig a
getCaseType (MkCase xt types _) = MkXtorSig xt types

-- only defined for fully opened terms, i.e. no de brujin indices left
typedTermToType :: Environment -> Term pc SimpleType -> Either Error SimpleType
typedTermToType _ (FreeVar _ _ t)        =  return t
typedTermToType _ (BoundVar _ _)     = Left $ (OtherError  "typedTermToType: found dangling bound variable")
-- Structural XtorCalls
typedTermToType env (XtorCall PrdRep xt@(MkXtorName { xtorNominalStructural = Structural }) args) = do
  argTypes <- argsToTypes env args
  return (TySimple Data [MkXtorSig xt argTypes])
typedTermToType env (XtorCall CnsRep xt@(MkXtorName { xtorNominalStructural = Structural }) args) = do
  argTypes <- argsToTypes env args
  return (TySimple Codata [MkXtorSig xt argTypes])
-- Nominal XtorCalls
typedTermToType env (XtorCall _ xt@(MkXtorName { xtorNominalStructural = Nominal }) _) =
  case lookupXtor xt env of
    Nothing -> Left $ OtherError "Xtor does not exist"
    Just tn -> return $ TyNominal (data_name tn)
-- Structural Matches
typedTermToType _ (Match PrdRep Structural cases) = return $ TySimple Codata (getCaseType <$> cases)
typedTermToType _ (Match CnsRep Structural cases) = return $ TySimple Data (getCaseType <$> cases)
-- Nominal Matches.
-- We know that empty matches cannot be parsed as nominal, so it is save to take the head of the xtors.
typedTermToType _ (Match _ Nominal []) = Left $ OtherError "unreachable"
typedTermToType env (Match _ Nominal (pmcase:pmcases)) =
  case lookupXtor (case_name pmcase) env of
    Nothing -> Left $ OtherError "Xtor does not exist"
    Just tn -> do
      forM_ pmcases (\MkCase { case_name } -> case_name `isContainedIn` (data_xtors tn))
      return $ TyNominal (data_name tn)
typedTermToType _ (MuAbs _ t _) = return t

isContainedIn :: XtorName -> [XtorSig SimpleType] -> Either Error ()
isContainedIn xt foo =
  if or (isContainedIn' <$> foo)
  then return ()
  else Left $ OtherError ("Pattern match fail with xtor" ++ ppPrint xt)
    where
      isContainedIn' :: XtorSig SimpleType -> Bool
      isContainedIn' MkXtorSig { sig_name } | xt == sig_name = True
                                            | otherwise      = False


getConstraintsTerm :: Environment -> Term pc SimpleType -> Either Error [Constraint]
getConstraintsTerm _ (BoundVar _ _) = Left $ OtherError "getConstraintsTerm:  found dangling bound variable"
getConstraintsTerm _ (FreeVar _ _ _) = return []
getConstraintsTerm env (XtorCall _ _ (MkXtorArgs prdargs cnsargs)) = do
  prdCss <- sequence $ getConstraintsTerm env <$> prdargs
  cnsCss <- sequence $ getConstraintsTerm env <$> cnsargs
  return $ (concat) (prdCss ++ cnsCss)
getConstraintsTerm env (Match _ _ cases) = do
  constraints <- sequence $ (\(MkCase _ _ cmd) -> getConstraintsCommand env cmd) <$> cases
  return $ concat constraints
getConstraintsTerm env (MuAbs _ _ cmd) = getConstraintsCommand env cmd

getConstraintsCommand :: Environment -> Command SimpleType -> Either Error [Constraint]
getConstraintsCommand _ Done = return []
getConstraintsCommand env (Print t) = getConstraintsTerm env t
getConstraintsCommand env (Apply t1 t2) = do
  css1 <- getConstraintsTerm env t1
  css2 <- getConstraintsTerm env t2
  ty1 <- typedTermToType env t1
  ty2 <- typedTermToType env t2
  return $ (SubType ty1 ty2) : (css1 ++ css2)

generateConstraints :: Term pc ()
                    -> Environment
                    -> Either Error (Term pc SimpleType, ConstraintSet)
generateConstraints t0 env = do
  termLocallyClosed t0
  (t1, GenerateState numVars _) <- runExcept (runStateT (annotateTerm t0) (GenerateState 0 env))
  css <- getConstraintsTerm env t1
  let constraintSet = ConstraintSet css (MkUVar <$> [0..numVars-1])
  return (t1, constraintSet)


