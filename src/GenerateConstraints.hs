module GenerateConstraints
  ( generateConstraints
  , typedTermToType
  ) where

import Control.Monad.State
import Control.Monad.Except

import Syntax.Terms
import Syntax.Types
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

data GenerateState = GenerateState { varGen :: Int }
type GenerateM a = StateT GenerateState (Except String) a

lookupCase :: XtorName -> GenerateM (Twice [SimpleType], XtorArgs SimpleType)
lookupCase _xt = throwError "not implemented yet"

freshVars :: Int -> PrdCnsRep pc -> GenerateM [(SimpleType, Term pc SimpleType)]
freshVars k pc = do
  n <- gets varGen
  modify (\gs@GenerateState { varGen } -> gs {varGen = varGen + k })
  return [(uv, FreeVar pc ("x" ++ show i) uv) | i <- [n..n+k-1], let uv = TyVar (MkUVar i)]

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
annotateTerm (FreeVar _ v _)     = throwError $ "Unknown free variable: \"" ++ v ++ "\""
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

-- only defined for fully opened terms, i.e. no de brujin indices left
typedTermToType :: Term pc SimpleType -> SimpleType
typedTermToType (FreeVar _ _ t)        =  t
typedTermToType (BoundVar _ _)     = error "typedTermToType: found dangling bound variable"
typedTermToType (XtorCall pc xt (MkXtorArgs prdargs cnsargs)) =
  SimpleType (case pc of PrdRep -> Data; CnsRep -> Codata) [MkXtorSig xt (Twice (typedTermToType <$> prdargs) (typedTermToType <$> cnsargs))]
typedTermToType (Match pc _ cases)      =
  SimpleType (case pc of PrdRep -> Codata; CnsRep -> Data) (map getCaseType cases)
  where
    getCaseType (MkCase xt types _) = MkXtorSig xt types
typedTermToType (MuAbs _ t _)        = t

getConstraintsTerm :: Term pc SimpleType -> [Constraint]
getConstraintsTerm (BoundVar _ _) = error "getConstraintsTerm:  found dangling bound variable"
getConstraintsTerm (FreeVar _ _ _)    = []
getConstraintsTerm (XtorCall _ _ (MkXtorArgs prdargs cnsargs)) =
  concat $ mergeTwice (++) $ Twice (getConstraintsTerm <$> prdargs) (getConstraintsTerm <$> cnsargs)
getConstraintsTerm (Match _ _ cases) = concat $ map (\(MkCase _ _ cmd) -> getConstraintsCommand cmd) cases
getConstraintsTerm (MuAbs _ _ cmd) = getConstraintsCommand cmd

getConstraintsCommand :: Command SimpleType -> [Constraint]
getConstraintsCommand Done = []
getConstraintsCommand (Print t) = getConstraintsTerm t
getConstraintsCommand (Apply t1 t2) = newCs : (getConstraintsTerm t1 ++ getConstraintsTerm t2)
  where newCs = SubType (typedTermToType t1) (typedTermToType t2)

generateConstraints :: Term pc () -> Either Error (Term pc SimpleType, [Constraint], [UVar])
generateConstraints t0 =
  case termLocallyClosed t0 of
    True -> case runExcept (runStateT (annotateTerm t0) (GenerateState 0)) of
      Right (t1, GenerateState numVars) -> Right (t1, getConstraintsTerm t1, MkUVar <$> [0..numVars-1])
      Left err            -> Left $ GenConstraintsError err
    False -> Left $ GenConstraintsError "Term is not locally closed"

