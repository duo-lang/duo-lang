{-# LANGUAGE NamedFieldPuns #-}
module Eval where

import Prettyprinter
import Data.List (elemIndex,find)
import Data.Maybe (fromJust, isJust)
import Data.Map (Map)
import qualified Data.Map as M

import Syntax.Terms
import Utils
import Pretty

type Environment a = Map String a

getArg :: Int -> PrdCnsRep pc -> XtorArgs a -> Term pc a
getArg j PrdRep (MkXtorArgs prds _) = prds !! j
getArg j CnsRep (MkXtorArgs _ cnss) = cnss !! j

termOpeningRec :: Int -> XtorArgs a -> Term pc a -> Term pc a
termOpeningRec k args bv@(BoundVar pc (i,j)) | i == k    = getArg j pc args
                                             | otherwise = bv
termOpeningRec _ _ fv@(FreeVar _ _ _)       = fv
termOpeningRec k args (XtorCall s xt (MkXtorArgs prdArgs cnsArgs)) =
  XtorCall s xt (MkXtorArgs (termOpeningRec k args <$> prdArgs)
                            (termOpeningRec k args <$> cnsArgs))
termOpeningRec k args (Match s cases) =
  Match s $ map (\pmcase@MkCase{ case_cmd } -> pmcase { case_cmd = commandOpeningRec (k+1) args case_cmd }) cases
termOpeningRec k args (MuAbs pc a cmd) =
  MuAbs pc a (commandOpeningRec (k+1) args cmd)

commandOpeningRec :: Int -> XtorArgs a -> Command a -> Command a
commandOpeningRec _ _ Done = Done
commandOpeningRec k args (Print t) = Print (termOpeningRec k args t)
commandOpeningRec k args (Apply t1 t2) = Apply (termOpeningRec k args t1) (termOpeningRec k args t2)

-- replaces bound variables pointing "outside" of a term with given arguments
termOpening :: XtorArgs a -> Term pc a -> Term pc a
termOpening = termOpeningRec 0

-- replaces single bound variable with given term (used for mu abstractions)
termOpeningSingle :: PrdCnsRep pc -> Term pc a -> Term pc' a -> Term pc' a
termOpeningSingle PrdRep t = termOpening (MkXtorArgs [t] [])
termOpeningSingle CnsRep t = termOpening (MkXtorArgs [] [t])

-- replaces bound variables pointing "outside" of a command with given arguments
commandOpening :: XtorArgs a -> Command a -> Command a
commandOpening = commandOpeningRec 0

commandOpeningSingle :: PrdCnsRep pc -> Term pc a -> Command a -> Command a
commandOpeningSingle PrdRep t = commandOpening (MkXtorArgs [t] [])
commandOpeningSingle CnsRep t = commandOpening (MkXtorArgs [] [t])


-- TODO: The logic here is not 100% correct!
termClosingRec :: Int -> Twice [FreeVarName] -> Term pc a -> Term pc a
termClosingRec _ _ bv@(BoundVar _ _) = bv
termClosingRec k (Twice prdvars cnsvars) (FreeVar PrdRep v a) | isJust (v `elemIndex` prdvars) = BoundVar PrdRep (k, fromJust (v `elemIndex` prdvars))
                                                              | isJust (v `elemIndex` cnsvars) = BoundVar PrdRep (k, fromJust (v `elemIndex` cnsvars))
                                                              | otherwise = FreeVar PrdRep v a
termClosingRec k (Twice prdvars cnsvars) (FreeVar CnsRep v a) | isJust (v `elemIndex` prdvars) = BoundVar CnsRep (k, fromJust (v `elemIndex` prdvars))
                                                              | isJust (v `elemIndex` cnsvars) = BoundVar CnsRep (k, fromJust (v `elemIndex` cnsvars))
                                                              | otherwise = FreeVar CnsRep v a
termClosingRec k vars (XtorCall s xt (MkXtorArgs prdArgs cnsArgs)) =
  XtorCall s xt (MkXtorArgs (termClosingRec k vars <$> prdArgs)(termClosingRec k vars <$> cnsArgs))
termClosingRec k vars (Match s cases) =
  Match s $ map (\pmcase@MkCase { case_cmd } -> pmcase { case_cmd = commandClosingRec (k+1) vars case_cmd }) cases
termClosingRec k vars (MuAbs pc a cmd) =
  MuAbs pc a (commandClosingRec (k+1) vars cmd)

commandClosingRec :: Int -> Twice [FreeVarName] -> Command a -> Command a
commandClosingRec _ _ Done = Done
commandClosingRec k args (Print t) = Print (termClosingRec k args t)
commandClosingRec k args (Apply t1 t2) = Apply (termClosingRec k args t1) (termClosingRec k args t2)

-- replaces given set of free variables with bound variables (de bruijn indices)
termClosing :: Twice [FreeVarName] -> Term pc a -> Term pc a
termClosing = termClosingRec 0

termClosingSingle :: PrdCns -> FreeVarName -> Term pc a -> Term pc a
termClosingSingle Prd v = termClosing (Twice [v] [])
termClosingSingle Cns v = termClosing (Twice [] [v])

commandClosing :: Twice [FreeVarName] -> Command a -> Command a
commandClosing = commandClosingRec 0

commandClosingSingle :: PrdCnsRep pc -> FreeVarName -> Command a -> Command a
commandClosingSingle PrdRep v = commandClosing (Twice [v] [])
commandClosingSingle CnsRep v = commandClosing (Twice [] [v])

-- substition can be defined in terms of opening and closing
substituteTerm :: Twice [FreeVarName] -> XtorArgs a -> Term pc a -> Term pc a
substituteTerm vars args = termOpening args . termClosing vars

substituteEnvTerm :: Environment (Term Prd a) -> Term Prd a -> Term Prd a
substituteEnvTerm env = substituteTerm (Twice (M.keys env) []) (MkXtorArgs (M.elems env) [])

substituteCommand :: Twice [FreeVarName] -> XtorArgs a -> Command a -> Command a
substituteCommand vars args (Apply t1 t2) = Apply (substituteTerm vars args t1) (substituteTerm vars args t2)
substituteCommand _ _ Done                = Done
substituteCommand vars args (Print t)     = Print $ substituteTerm vars args t

substituteEnvCommand :: Environment (Term Prd a) -> Command a -> Command a
substituteEnvCommand env = substituteCommand (Twice (M.keys env) []) (MkXtorArgs (M.elems env) [])

lcAt_term :: Int -> Term pc a -> Bool
lcAt_term k (BoundVar _ (i,_))                 = i < k
lcAt_term _ (FreeVar _ _ _)                    = True
lcAt_term k (XtorCall _ _ (MkXtorArgs prds cnss)) = all (lcAt_term k) prds && all (lcAt_term k) cnss
lcAt_term k (Match _ cases)                  = all (\MkCase { case_cmd } -> lcAt_cmd (k+1) case_cmd) cases
lcAt_term k (MuAbs _ _ cmd)                  = lcAt_cmd (k+1) cmd

-- tests if a term is locally closed, i.e. contains no de brujin indices pointing outside of the term
isLc_term :: Term Prd a -> Bool
isLc_term = lcAt_term 0

lcAt_cmd :: Int -> Command a -> Bool
lcAt_cmd k (Apply t1 t2) = lcAt_term k t1 && lcAt_term k t2
lcAt_cmd _ _           = True

isLc_cmd :: Command a -> Bool
isLc_cmd = lcAt_cmd 0

freeVars_term :: Term pc a -> [FreeVarName]
freeVars_term (BoundVar _ _)                 = []
freeVars_term (FreeVar _ v _)                    = [v]
freeVars_term (XtorCall _ _ (MkXtorArgs prds cnss)) = concat $ map freeVars_term prds ++ map freeVars_term cnss
freeVars_term (Match _ cases)                  = concat $ map (\MkCase { case_cmd } -> freeVars_cmd case_cmd) cases
freeVars_term (MuAbs _ _ cmd)                  = freeVars_cmd cmd

freeVars_cmd :: Command a -> [FreeVarName]
freeVars_cmd (Apply t1 t2) = freeVars_term t1 ++ freeVars_term t2
freeVars_cmd _             = []

-- tests if a term is closed, i.e. contains no free variables
isClosed_term :: Term Prd a -> Bool
isClosed_term t = freeVars_term t == []

isClosed_cmd :: Command a -> Bool
isClosed_cmd cmd = freeVars_cmd cmd == []

lookupCase :: XtorName -> [Case a] -> Either Error (Case a)
lookupCase xt cases = case find (\MkCase { case_name } -> xt == case_name) cases of
  Just pmcase -> Right pmcase
  Nothing -> Left $ EvalError $ unlines ["Error during evaluation. The xtor: "
                                        , unXtorName xt
                                        , "doesn't occur in match."
                                        ]

eval :: Pretty a => Command a -> Either Error String
eval Done = Right "Done"
eval (Print t) = Right $ ppPrint t
eval cmd@(Apply (XtorCall PrdRep xt args) (Match CnsRep cases)) = do
  (MkCase _ argTypes cmd') <- lookupCase xt cases
  if True -- TODO fmap length argTypes == fmap length args
    then eval $ commandOpening args cmd' --reduction is just opening
    else Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                           "\"\nArgument lengths don't coincide.")
eval cmd@(Apply (Match PrdRep cases) (XtorCall CnsRep xt args)) = do
  (MkCase _ argTypes cmd') <- lookupCase xt cases
  if True -- TODO fmap length argTypes == fmap length args
    then eval $ commandOpening args cmd' --reduction is just opening
    else Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                            "\"\nArgument lengths don't coincide.")
eval (Apply (MuAbs PrdRep _ cmd) cns) = eval $ commandOpeningSingle CnsRep cns cmd
eval (Apply prd (MuAbs CnsRep _ cmd)) = eval $ commandOpeningSingle PrdRep prd cmd
-- Error handling
eval cmd@(Apply _ _) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                          "\"\n Free variable encountered!")
