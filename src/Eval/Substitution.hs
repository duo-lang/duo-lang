module Eval.Substitution
  ( -- Variable Opening
    commandOpening
  , commandOpeningSingle
    -- Variable Closing
  , commandClosing
  , commandClosingSingle
  -- Locally Closed Check
  , termLocallyClosed
  , commandLocallyClosed
  , checkIfBound
  -- Free Variables
  , isClosed_term
  ) where

import Data.Containers.ListUtils (nubOrd)
import Data.List (elemIndex)
-- import Data.Map (Map)
-- import qualified Data.Map as M
import Data.Maybe (fromJust, isJust)

import Utils
import Syntax.SymmetricTerm

---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

termOpeningRec :: Int -> XtorArgs a -> Term pc a -> Term pc a
termOpeningRec k MkXtorArgs { prdArgs } bv@(BoundVar PrdRep (i,j)) | i == k    = prdArgs !! j
                                                                   | otherwise = bv
termOpeningRec k MkXtorArgs { cnsArgs } bv@(BoundVar CnsRep (i,j)) | i == k    = cnsArgs !! j
                                                                   | otherwise = bv
termOpeningRec _ _ fv@(FreeVar _ _ _)       = fv
termOpeningRec k args (XtorCall s xt (MkXtorArgs prdArgs cnsArgs)) =
  XtorCall s xt (MkXtorArgs (termOpeningRec k args <$> prdArgs)
                            (termOpeningRec k args <$> cnsArgs))
termOpeningRec k args (XMatch pc sn cases) =
  XMatch pc sn $ map (\pmcase@MkCase{ case_cmd } -> pmcase { case_cmd = commandOpeningRec (k+1) args case_cmd }) cases
termOpeningRec k args (MuAbs pc a cmd) =
  MuAbs pc a (commandOpeningRec (k+1) args cmd)

commandOpeningRec :: Int -> XtorArgs a -> Command a -> Command a
commandOpeningRec _ _ Done = Done
commandOpeningRec k args (Print t) = Print (termOpeningRec k args t)
commandOpeningRec k args (Apply t1 t2) = Apply (termOpeningRec k args t1) (termOpeningRec k args t2)

-- -- replaces bound variables pointing "outside" of a term with given arguments
-- termOpening :: XtorArgs a -> Term pc a -> Term pc a
-- termOpening = termOpeningRec 0

-- -- replaces single bound variable with given term (used for mu abstractions)
-- termOpeningSingle :: PrdCnsRep pc -> Term pc a -> Term pc' a -> Term pc' a
-- termOpeningSingle PrdRep t = termOpening (MkXtorArgs [t] [])
-- termOpeningSingle CnsRep t = termOpening (MkXtorArgs [] [t])

-- replaces bound variables pointing "outside" of a command with given arguments
commandOpening :: XtorArgs a -> Command a -> Command a
commandOpening = commandOpeningRec 0

commandOpeningSingle :: PrdCnsRep pc -> Term pc a -> Command a -> Command a
commandOpeningSingle PrdRep t = commandOpening (MkXtorArgs [t] [])
commandOpeningSingle CnsRep t = commandOpening (MkXtorArgs [] [t])

---------------------------------------------------------------------------------
-- Variable Closing
---------------------------------------------------------------------------------

termClosingRec :: Int -> Twice [FreeVarName] -> Term pc a -> Term pc a
termClosingRec _ _ bv@(BoundVar _ _) = bv
termClosingRec k (Twice prdvars _) (FreeVar PrdRep v a) | isJust (v `elemIndex` prdvars) = BoundVar PrdRep (k, fromJust (v `elemIndex` prdvars))
                                                        | otherwise = FreeVar PrdRep v a
termClosingRec k (Twice _ cnsvars) (FreeVar CnsRep v a) | isJust (v `elemIndex` cnsvars) = BoundVar CnsRep (k, fromJust (v `elemIndex` cnsvars))
                                                        | otherwise = FreeVar CnsRep v a
termClosingRec k vars (XtorCall s xt (MkXtorArgs prdArgs cnsArgs)) =
  XtorCall s xt (MkXtorArgs (termClosingRec k vars <$> prdArgs)(termClosingRec k vars <$> cnsArgs))
termClosingRec k vars (XMatch pc sn cases) =
  XMatch pc sn $ map (\pmcase@MkCase { case_cmd } -> pmcase { case_cmd = commandClosingRec (k+1) vars case_cmd }) cases
termClosingRec k vars (MuAbs pc a cmd) =
  MuAbs pc a (commandClosingRec (k+1) vars cmd)

commandClosingRec :: Int -> Twice [FreeVarName] -> Command a -> Command a
commandClosingRec _ _ Done = Done
commandClosingRec k args (Print t) = Print (termClosingRec k args t)
commandClosingRec k args (Apply t1 t2) = Apply (termClosingRec k args t1) (termClosingRec k args t2)

-- -- replaces given set of free variables with bound variables (de bruijn indices)
-- termClosing :: Twice [FreeVarName] -> Term pc a -> Term pc a
-- termClosing = termClosingRec 0

-- termClosingSingle :: PrdCns -> FreeVarName -> Term pc a -> Term pc a
-- termClosingSingle Prd v = termClosing (Twice [v] [])
-- termClosingSingle Cns v = termClosing (Twice [] [v])

commandClosing :: Twice [FreeVarName] -> Command a -> Command a
commandClosing = commandClosingRec 0

commandClosingSingle :: PrdCnsRep pc -> FreeVarName -> Command a -> Command a
commandClosingSingle PrdRep v = commandClosing (Twice [v] [])
commandClosingSingle CnsRep v = commandClosing (Twice [] [v])

---------------------------------------------------------------------------------
-- Substitution
---------------------------------------------------------------------------------

-- -- substition can be defined in terms of opening and closing
-- substituteTerm :: Twice [FreeVarName] -> XtorArgs a -> Term pc a -> Term pc a
-- substituteTerm vars args = termOpening args . termClosing vars

-- -- substituteEnvTerm :: Environment (Term Prd a) -> Term Prd a -> Term Prd a
-- -- substituteEnvTerm env = substituteTerm (Twice (M.keys env) []) (MkXtorArgs (M.elems env) [])

-- substituteCommand :: Twice [FreeVarName] -> XtorArgs a -> Command a -> Command a
-- substituteCommand vars args (Apply t1 t2) = Apply (substituteTerm vars args t1) (substituteTerm vars args t2)
-- substituteCommand _ _ Done                = Done
-- substituteCommand vars args (Print t)     = Print $ substituteTerm vars args t

-- substituteEnvCommand :: Environment (Term Prd a) -> Command a -> Command a
-- substituteEnvCommand env = substituteCommand (Twice (M.keys env) []) (MkXtorArgs (M.elems env) [])

---------------------------------------------------------------------------------
-- Check for locally closedness
---------------------------------------------------------------------------------

checkIfBound :: [Twice [a]] -> PrdCnsRep pc -> Index -> Either Error ()
checkIfBound env rep  (i, j) | i >= length env = Left $ OtherError "Variable is not bound"
                             | otherwise = checkIfBound' (env !! i) rep j

checkIfBound' :: Twice [a] -> PrdCnsRep pc -> Int -> Either Error ()
checkIfBound' (Twice prds _) PrdRep j = if j < length prds then Right () else Left $ OtherError "Variable is not bound"
checkIfBound' (Twice _ cnss) CnsRep j = if j < length cnss then Right () else Left $ OtherError "Variable is not bound"

termLocallyClosedRec :: [Twice [()]] -> Term pc a -> Either Error ()
termLocallyClosedRec env (BoundVar pc idx) = checkIfBound env pc idx
termLocallyClosedRec _ (FreeVar _ _ _) = Right ()
termLocallyClosedRec env (XtorCall _ _ (MkXtorArgs prds cnss)) = do
  sequence_ (termLocallyClosedRec env <$> prds)
  sequence_ (termLocallyClosedRec env <$> cnss)
termLocallyClosedRec env (XMatch _ _ cases) = do
  sequence_ ((\MkCase { case_cmd, case_args } -> commandLocallyClosedRec (twiceMap (fmap (const ())) (fmap (const ())) case_args : env) case_cmd) <$> cases)
termLocallyClosedRec env (MuAbs PrdRep _ cmd) = commandLocallyClosedRec (Twice [] [()] : env) cmd
termLocallyClosedRec env (MuAbs CnsRep _ cmd) = commandLocallyClosedRec (Twice [()] [] : env) cmd

commandLocallyClosedRec :: [Twice [()]] -> Command a -> Either Error ()
commandLocallyClosedRec _ Done = Right ()
commandLocallyClosedRec env (Print t) = termLocallyClosedRec env t
commandLocallyClosedRec env (Apply t1 t2) = termLocallyClosedRec env t1 >> termLocallyClosedRec env t2

termLocallyClosed :: Term pc a -> Either Error ()
termLocallyClosed = termLocallyClosedRec []

commandLocallyClosed :: Command a -> Either Error ()
commandLocallyClosed = commandLocallyClosedRec []

---------------------------------------------------------------------------------
-- Compute set of free variables and check if term is closed
---------------------------------------------------------------------------------

combineFreeVars :: [Twice[FreeVarName]] -> Twice [FreeVarName]
combineFreeVars = foldr combineFreeVars' (Twice [] [])
  where
    combineFreeVars' :: Twice [FreeVarName] -> Twice [FreeVarName] -> Twice [FreeVarName]
    combineFreeVars' (Twice prds1 cnss1) (Twice prds2 cnss2) = Twice (nubOrd (prds1 ++ prds2)) (nubOrd (cnss1 ++ cnss2))

freeVars_term :: Term pc a -> Twice [FreeVarName]
freeVars_term (BoundVar _ _) = Twice [] []
freeVars_term (FreeVar PrdRep v _) = Twice [v] []
freeVars_term (FreeVar CnsRep v _) = Twice [] [v]
freeVars_term (XtorCall _ _ (MkXtorArgs prds cnss)) = combineFreeVars (map freeVars_term prds ++ map freeVars_term cnss)
freeVars_term (XMatch _ _ cases)                  = combineFreeVars (map (\MkCase { case_cmd } -> freeVars_cmd case_cmd) cases)
freeVars_term (MuAbs _ _ cmd)                  = freeVars_cmd cmd

freeVars_cmd :: Command a -> Twice [FreeVarName]
freeVars_cmd (Apply t1 t2) = combineFreeVars [freeVars_term t1, freeVars_term t2]
freeVars_cmd _             = Twice [] []

-- tests if a term is closed, i.e. contains no free variables
isClosed_term :: Term Prd a -> Bool
isClosed_term t = freeVars_term t == Twice [] []

-- isClosed_cmd :: Command a -> Bool
-- isClosed_cmd cmd = freeVars_cmd cmd == []

