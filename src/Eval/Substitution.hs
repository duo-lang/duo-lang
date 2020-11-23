module Eval.Substitution
  ( commandClosing
  , commandClosingSingle
  , commandOpening
  , commandOpeningSingle
  , isClosed_term
  , isLc_term
  ) where

import Data.List (elemIndex)
import Control.Applicative ((<|>))
import Data.Maybe (fromJust)
import qualified Data.Map as M
import Syntax.Terms
import Utils

termOpeningRec :: Int -> XtorArgs a -> Term a -> Term a
termOpeningRec k args (BoundVar i pc j)     = if i == k then getArg j pc args else BoundVar i pc j
termOpeningRec _ _ (FreeVar n a)            = FreeVar n a
termOpeningRec k args (XtorCall s xt args') =
  XtorCall s xt $ (fmap.fmap) (termOpeningRec k args) args'
termOpeningRec k args (Match s cases) =
  Match s $ map (\(xtn,xtty,cmd) -> (xtn,xtty, commandOpeningRec (k+1) args cmd)) cases
termOpeningRec k args (MuAbs pc a cmd) =
  MuAbs pc a (commandOpeningRec (k+1) args cmd)

commandOpeningRec :: Int -> XtorArgs a -> Command a -> Command a
commandOpeningRec _ _ Done = Done
commandOpeningRec k args (Print t) = Print (termOpeningRec k args t)
commandOpeningRec k args (Apply t1 t2) = Apply (termOpeningRec k args t1) (termOpeningRec k args t2)

-- replaces bound variables pointing "outside" of a term with given arguments
termOpening :: XtorArgs a -> Term a -> Term a
termOpening = termOpeningRec 0

-- replaces single bound variable with given term (used for mu abstractions)
termOpeningSingle :: PrdOrCns -> Term a -> Term a -> Term a
termOpeningSingle Prd t = termOpening (Twice [t] [])
termOpeningSingle Cns t = termOpening (Twice [] [t])

-- replaces bound variables pointing "outside" of a command with given arguments
commandOpening :: XtorArgs a -> Command a -> Command a
commandOpening = commandOpeningRec 0

commandOpeningSingle :: PrdOrCns -> Term a -> Command a -> Command a
commandOpeningSingle Prd t = commandOpening (Twice [t] [])
commandOpeningSingle Cns t = commandOpening (Twice [] [t])


termClosingRec :: Int -> Twice [FreeVarName] -> Term a -> Term a
termClosingRec _ _ (BoundVar i pc j) = BoundVar i pc j
termClosingRec k (Twice prdvars cnsvars) (FreeVar v a) = fromJust $ --no need to worry, last alternative cannot fail
  (BoundVar k Prd <$> (v `elemIndex` prdvars)) <|>
  (BoundVar k Cns <$> (v `elemIndex` cnsvars)) <|>
  (Just (FreeVar v a))
termClosingRec k vars (XtorCall s xt args) = XtorCall s xt $ (fmap . fmap) (termClosingRec k vars) args
termClosingRec k vars (Match s cases) =
  Match s $ map (\(xtn,xtty,cmd) -> (xtn,xtty, commandClosingRec (k+1) vars cmd)) cases
termClosingRec k vars (MuAbs pc a cmd) =
  MuAbs pc a (commandClosingRec (k+1) vars cmd)

commandClosingRec :: Int -> Twice [FreeVarName] -> Command a -> Command a
commandClosingRec _ _ Done = Done
commandClosingRec k args (Print t) = Print (termClosingRec k args t)
commandClosingRec k args (Apply t1 t2) = Apply (termClosingRec k args t1) (termClosingRec k args t2)

-- replaces given set of free variables with bound variables (de bruijn indices)
termClosing :: Twice [FreeVarName] -> Term a -> Term a
termClosing = termClosingRec 0

termClosingSingle :: PrdOrCns -> FreeVarName -> Term a -> Term a
termClosingSingle Prd v = termClosing (Twice [v] [])
termClosingSingle Cns v = termClosing (Twice [] [v])

commandClosing :: Twice [FreeVarName] -> Command a -> Command a
commandClosing = commandClosingRec 0

commandClosingSingle :: PrdOrCns -> FreeVarName -> Command a -> Command a
commandClosingSingle Prd v = commandClosing (Twice [v] [])
commandClosingSingle Cns v = commandClosing (Twice [] [v])

-- substition can be defined in terms of opening and closing
substituteTerm :: Twice [FreeVarName] -> XtorArgs a -> Term a -> Term a
substituteTerm vars args = termOpening args . termClosing vars

substituteEnvTerm :: Environment (Term a) -> Term a -> Term a
substituteEnvTerm env = substituteTerm (Twice (M.keys env) []) (Twice (M.elems env) [])

substituteCommand :: Twice [FreeVarName] -> XtorArgs a -> Command a -> Command a
substituteCommand vars args (Apply t1 t2) = Apply (substituteTerm vars args t1) (substituteTerm vars args t2)
substituteCommand _ _ Done                = Done
substituteCommand vars args (Print t)     = Print $ substituteTerm vars args t

substituteEnvCommand :: Environment (Term a) -> Command a -> Command a
substituteEnvCommand env = substituteCommand (Twice (M.keys env) []) (Twice (M.elems env) [])

lcAt_term :: Int -> Term a -> Bool
lcAt_term k (BoundVar i _ _)                 = i < k
lcAt_term _ (FreeVar _ _)                    = True
lcAt_term k (XtorCall _ _ (Twice prds cnss)) = all (lcAt_term k) prds && all (lcAt_term k) cnss
lcAt_term k (Match _ cases)                  = all (\(_,_,cmd) -> lcAt_cmd (k+1) cmd) cases
lcAt_term k (MuAbs _ _ cmd)                  = lcAt_cmd (k+1) cmd

-- tests if a term is locally closed, i.e. contains no de brujin indices pointing outside of the term
isLc_term :: Term a -> Bool
isLc_term = lcAt_term 0

lcAt_cmd :: Int -> Command a -> Bool
lcAt_cmd k (Apply t1 t2) = lcAt_term k t1 && lcAt_term k t2
lcAt_cmd _ _           = True

isLc_cmd :: Command a -> Bool
isLc_cmd = lcAt_cmd 0

freeVars_term :: Term a -> [FreeVarName]
freeVars_term (BoundVar _ _ _)                 = []
freeVars_term (FreeVar v _)                    = [v]
freeVars_term (XtorCall _ _ (Twice prds cnss)) = concat $ map freeVars_term prds ++ map freeVars_term cnss
freeVars_term (Match _ cases)                  = concat $ map (\(_,_,cmd) -> freeVars_cmd cmd) cases
freeVars_term (MuAbs _ _ cmd)                  = freeVars_cmd cmd

freeVars_cmd :: Command a -> [FreeVarName]
freeVars_cmd (Apply t1 t2) = freeVars_term t1 ++ freeVars_term t2
freeVars_cmd _             = []

-- tests if a term is closed, i.e. contains no free variables
isClosed_term :: Term a -> Bool
isClosed_term t = freeVars_term t == []

isClosed_cmd :: Command a -> Bool
isClosed_cmd cmd = freeVars_cmd cmd == []
