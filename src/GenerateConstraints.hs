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
import Pretty

{-
Constraint generation is split in two phases:

  1) The term is annotated with fresh unification variables
  2) The term is traversed and constraints are collected

This seperation is only possible because in our system, there is a 1-to-1 correspondence between program variables
and unifcation variables. Thus, during the actual constraint generation, we don't ever have to come up with new
unifcation variables.
-}

--------------------------------------------------------------------------------------------
-- Phase 0: Term sanity check (not strictly part of constraint generation)
-- Here, we check if the parsed term is syntactically correct in the following sense:
-- ** Producers are only in places where producers can go and consumers are only in places consumers can go **
-- This could be done during pasrsing, *IF* we were to use different variable names to distinguish producers
-- from consumers. We do so only in the mathematical formaliazation of the syntax, but not in the implementation.
-- So instead, we do a santiy check right after parsing.
--------------------------------------------------------------------------------------------

isValidTerm' :: PrdOrCns -> Term () -> Except String ()
isValidTerm' pc (BoundVar _ pc' _) =
  if pc == pc' then return ()
    else throwError "Sanity check failed, you used a prd/cns variable in a wrong position.\nSorry, I can't be more precise since we're using de brujin indices and not variable names ;)"
isValidTerm' _ (FreeVar _ _)       = throwError "Sanity check failed, term is not closed."
isValidTerm' Prd (XtorCall Data _ (Twice prdArgs cnsArgs))
  = mapM_ (isValidTerm' Prd) prdArgs >> mapM_ (isValidTerm' Cns) cnsArgs
isValidTerm' Cns t@(XtorCall Data _ _) = throwError $ "Sanity check failed. Producer term \n\n" ++ ppPrint t ++ "\n\n used in consumer position."
isValidTerm' Cns (XtorCall Codata _ (Twice prdArgs cnsArgs))
  = mapM_ (isValidTerm' Prd) prdArgs >> mapM_ (isValidTerm' Cns) cnsArgs
isValidTerm' Prd t@(XtorCall Codata _ _) = throwError $ "Sanity check failed. Consumer term \n\n" ++ ppPrint t ++ "\n\n used in producer position."
isValidTerm' Prd (Match Codata cases) = mapM_ (\(_,_,cmd) -> isValidCmd cmd) cases
isValidTerm' Prd t@(Match Data _) = throwError $ "Sanity check failed. Consumer term \n\n" ++ ppPrint t ++ "\n\n used in producer position."
isValidTerm' Cns (Match Data cases) = mapM_ (\(_,_,cmd) -> isValidCmd cmd) cases
isValidTerm' Cns t@(Match Codata _) = throwError $ "Sanity check failed. Producer term \n\n" ++ ppPrint t ++ "\n\n used in consumer position."
isValidTerm' Prd (MuAbs Cns _ cmd) = isValidCmd cmd
isValidTerm' Prd t@(MuAbs Prd _ _) = throwError $ "Sanity check failed. Consumer term \n\n" ++ ppPrint t ++ "\n\n used in producer position."
isValidTerm' Cns (MuAbs Prd _ cmd) = isValidCmd cmd
isValidTerm' Cns t@(MuAbs Cns _ _) = throwError $ "Sanity check failed. Producer term \n\n" ++ ppPrint t ++ "\n\n used in consumer position."

isValidTerm :: Term () -> Except String ()
isValidTerm t = isValidTerm' (termPrdOrCns t) t

isValidCmd :: Command () -> Except String ()
isValidCmd Done = return ()
isValidCmd (Print t) = isValidTerm t
isValidCmd (Apply t1 t2) = isValidTerm' Prd t1 >> isValidTerm' Cns t2

-------------------------------------------------------------------------------------
-- Phase 1: Term annotation
-------------------------------------------------------------------------------------

type GenerateM a = StateT Int (Except String) a

freshVars :: Int -> GenerateM [(UVar, Term UVar)]
freshVars k = do
  n <- get
  modify (+k)
  return [(uv, FreeVar ("x" ++ show i) uv) | i <- [n..n+k-1], let uv = MkUVar i]

annotateTerm :: Term () -> GenerateM (Term UVar)
annotateTerm (FreeVar v _)     = throwError $ "Unknown free variable: \"" ++ v ++ "\""
annotateTerm (BoundVar i pc j) = return (BoundVar i pc j)
annotateTerm (XtorCall s xt (Twice prdArgs cnsArgs)) = do
  prdArgs' <- mapM annotateTerm prdArgs
  cnsArgs' <- mapM annotateTerm cnsArgs
  return (XtorCall s xt (Twice prdArgs' cnsArgs'))
annotateTerm (Match s cases) =
  Match s <$> forM cases (\(xt,Twice prds cnss,cmd) -> do
    (prdUVars, prdTerms) <- unzip <$> freshVars (length prds)
    (cnsUVars, cnsTerms) <- unzip <$> freshVars (length cnss)
    cmd' <- annotateCommand cmd
    return (xt, Twice prdUVars cnsUVars, (commandOpening (Twice prdTerms cnsTerms) cmd')))
annotateTerm (MuAbs pc _ cmd) = do
  (uv, freeVar) <- head <$> freshVars 1
  cmd' <- annotateCommand cmd
  return (MuAbs pc uv (commandOpeningSingle pc freeVar cmd'))

annotateCommand :: Command () -> GenerateM (Command UVar)
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
typedTermToType :: Term UVar -> SimpleType
typedTermToType (FreeVar _ t)        = TyVar t
typedTermToType (BoundVar _ _ _)     = error "typedTermToType: found dangling bound variable"
typedTermToType (XtorCall s xt args) = SimpleType s [(xt, (fmap . fmap) typedTermToType args)]
typedTermToType (Match s cases)      = SimpleType s $ map (\(xt,types,_) -> (xt, (fmap . fmap) TyVar types)) cases
typedTermToType (MuAbs _ t _)        = TyVar t

getConstraintsTerm :: Term UVar -> [Constraint]
getConstraintsTerm (BoundVar _ _ _) = error "getConstraintsTerm:  found dangling bound variable"
getConstraintsTerm (FreeVar _ _)    = []
getConstraintsTerm (XtorCall _ _ args) = concat $ mergeTwice (++) $ (fmap.fmap) getConstraintsTerm args
getConstraintsTerm (Match _ cases) = concat $ map (\(_,_,cmd) -> getConstraintsCommand cmd) cases
getConstraintsTerm (MuAbs _ _ cmd) = getConstraintsCommand cmd

getConstraintsCommand :: Command UVar -> [Constraint]
getConstraintsCommand Done = []
getConstraintsCommand (Print t) = getConstraintsTerm t
getConstraintsCommand (Apply t1 t2) = newCs : (getConstraintsTerm t1 ++ getConstraintsTerm t2)
  where newCs = SubType (typedTermToType t1) (typedTermToType t2)

generateConstraints :: Term () -> Either Error (Term UVar, [Constraint], [UVar])
generateConstraints t0 =
  case runExcept (isValidTerm t0) of
    Right () -> case runExcept (runStateT (annotateTerm t0) 0) of
      Right (t1, numVars) -> Right (t1, getConstraintsTerm t1, MkUVar <$> [0..numVars-1])
      Left err            -> Left $ GenConstraintsError err
    Left err -> Left $ GenConstraintsError err
