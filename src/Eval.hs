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

getArg :: Int -> PrdCns -> XtorArgs a -> Term Prd a
getArg j Prd (Twice prds _) = prds !! j
getArg j Cns (Twice _ cnss) = cnss !! j

termOpeningRec :: Int -> XtorArgs a -> Term Prd a -> Term Prd a
termOpeningRec k args (BoundVar (i,j) pc)     = if i == k then getArg j pc args else BoundVar (i,j) pc
termOpeningRec _ _ (FreeVar n a)            = FreeVar n a
termOpeningRec k args (XtorCall s xt args') =
  XtorCall s xt $ (fmap.fmap) (termOpeningRec k args) args'
termOpeningRec k args (Match s cases) =
  Match s $ map (\pmcase@MkCase{ case_cmd } -> pmcase { case_cmd = commandOpeningRec (k+1) args case_cmd }) cases
termOpeningRec k args (MuAbs pc a cmd) =
  MuAbs pc a (commandOpeningRec (k+1) args cmd)

commandOpeningRec :: Int -> XtorArgs a -> Command a -> Command a
commandOpeningRec _ _ Done = Done
commandOpeningRec k args (Print t) = Print (termOpeningRec k args t)
commandOpeningRec k args (Apply t1 t2) = Apply (termOpeningRec k args t1) (termOpeningRec k args t2)

-- replaces bound variables pointing "outside" of a term with given arguments
termOpening :: XtorArgs a -> Term Prd a -> Term Prd a
termOpening = termOpeningRec 0

-- replaces single bound variable with given term (used for mu abstractions)
termOpeningSingle :: PrdCns -> Term Prd a -> Term Prd a -> Term Prd a
termOpeningSingle Prd t = termOpening (Twice [t] [])
termOpeningSingle Cns t = termOpening (Twice [] [t])

-- replaces bound variables pointing "outside" of a command with given arguments
commandOpening :: XtorArgs a -> Command a -> Command a
commandOpening = commandOpeningRec 0

commandOpeningSingle :: PrdCns -> Term Prd a -> Command a -> Command a
commandOpeningSingle Prd t = commandOpening (Twice [t] [])
commandOpeningSingle Cns t = commandOpening (Twice [] [t])


termClosingRec :: Int -> Twice [FreeVarName] -> Term Prd a -> Term Prd a
termClosingRec _ _ bv@(BoundVar _ _) = bv
termClosingRec k (Twice prdvars cnsvars) (FreeVar v a) | isJust (v `elemIndex` prdvars) = BoundVar (k, fromJust (v `elemIndex` prdvars)) Prd
                                                       | isJust (v `elemIndex` cnsvars) = BoundVar (k, fromJust (v `elemIndex` cnsvars)) Cns
                                                       | otherwise = FreeVar v a
termClosingRec k vars (XtorCall s xt args) = XtorCall s xt $ (fmap . fmap) (termClosingRec k vars) args
termClosingRec k vars (Match s cases) =
  Match s $ map (\pmcase@MkCase { case_cmd } -> pmcase { case_cmd = commandClosingRec (k+1) vars case_cmd }) cases
termClosingRec k vars (MuAbs pc a cmd) =
  MuAbs pc a (commandClosingRec (k+1) vars cmd)

commandClosingRec :: Int -> Twice [FreeVarName] -> Command a -> Command a
commandClosingRec _ _ Done = Done
commandClosingRec k args (Print t) = Print (termClosingRec k args t)
commandClosingRec k args (Apply t1 t2) = Apply (termClosingRec k args t1) (termClosingRec k args t2)

-- replaces given set of free variables with bound variables (de bruijn indices)
termClosing :: Twice [FreeVarName] -> Term Prd a -> Term Prd a
termClosing = termClosingRec 0

termClosingSingle :: PrdCns -> FreeVarName -> Term Prd a -> Term Prd a
termClosingSingle Prd v = termClosing (Twice [v] [])
termClosingSingle Cns v = termClosing (Twice [] [v])

commandClosing :: Twice [FreeVarName] -> Command a -> Command a
commandClosing = commandClosingRec 0

commandClosingSingle :: PrdCns -> FreeVarName -> Command a -> Command a
commandClosingSingle Prd v = commandClosing (Twice [v] [])
commandClosingSingle Cns v = commandClosing (Twice [] [v])

-- substition can be defined in terms of opening and closing
substituteTerm :: Twice [FreeVarName] -> XtorArgs a -> Term Prd a -> Term Prd a
substituteTerm vars args = termOpening args . termClosing vars

substituteEnvTerm :: Environment (Term Prd a) -> Term Prd a -> Term Prd a
substituteEnvTerm env = substituteTerm (Twice (M.keys env) []) (Twice (M.elems env) [])

substituteCommand :: Twice [FreeVarName] -> XtorArgs a -> Command a -> Command a
substituteCommand vars args (Apply t1 t2) = Apply (substituteTerm vars args t1) (substituteTerm vars args t2)
substituteCommand _ _ Done                = Done
substituteCommand vars args (Print t)     = Print $ substituteTerm vars args t

substituteEnvCommand :: Environment (Term Prd a) -> Command a -> Command a
substituteEnvCommand env = substituteCommand (Twice (M.keys env) []) (Twice (M.elems env) [])

lcAt_term :: Int -> Term Prd a -> Bool
lcAt_term k (BoundVar (i,_) _)                 = i < k
lcAt_term _ (FreeVar _ _)                    = True
lcAt_term k (XtorCall _ _ (Twice prds cnss)) = all (lcAt_term k) prds && all (lcAt_term k) cnss
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

freeVars_term :: Term Prd a -> [FreeVarName]
freeVars_term (BoundVar _ _)                 = []
freeVars_term (FreeVar v _)                    = [v]
freeVars_term (XtorCall _ _ (Twice prds cnss)) = concat $ map freeVars_term prds ++ map freeVars_term cnss
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

eval :: Pretty a => Command a -> Either Error String
eval Done = Right "Done"
eval (Print t) = Right $ ppPrint t
eval cmd@(Apply (XtorCall Data xt args) (Match Data cases))
  = case (find (\MkCase { case_name } -> xt==case_name) cases) of
      Just (MkCase _ argTypes cmd') ->
        if fmap length argTypes == fmap length args
          then eval $ commandOpening args cmd' --reduction is just opening
          else Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                 "\"\nArgument lengths don't coincide.")
      Nothing -> Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                   "\"\nXtor \"" ++ unXtorName xt ++ "\" doesn't occur in match.")
eval cmd@(Apply (Match Codata cases) (XtorCall Codata xt args))
  = case (find (\(MkCase xt' _ _) -> xt==xt') cases) of
      Just (MkCase _ argTypes cmd') ->
        if fmap length argTypes == fmap length args
          then eval $ commandOpening args cmd' --reduction is just opening
          else Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                 "\"\nArgument lengths don't coincide.")
      Nothing -> Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                   "\"\nXtor \"" ++ unXtorName xt ++ "\" doesn't occur in match.")
eval (Apply (MuAbs Cns _ cmd) cns) = eval $ commandOpeningSingle Cns cns cmd
eval (Apply prd (MuAbs Prd _ cmd)) = eval $ commandOpeningSingle Prd prd cmd

-- Error handling
eval cmd@(Apply (XtorCall Codata _ _) _) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                       "\"\nLeft side is not a producer!")
eval cmd@(Apply _ (Match Codata _)) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                       "\"\nRight side is not a consumer!")
eval cmd@(Apply (Match Data _) _) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                       "\"\nLeft side is not a producer!")
eval cmd@(Apply _ (XtorCall Data _ _)) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                       "\"\nRight side is not a consumer!")
eval cmd@(Apply (MuAbs Prd _ _) _) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                       "\"\nLeft side is not a producer!")
eval cmd@(Apply _ (MuAbs Cns _ _)) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                       "\"\nRight side is not a consumer!")
eval cmd@(Apply _ _) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                          "\"\n Free variable encountered!")
