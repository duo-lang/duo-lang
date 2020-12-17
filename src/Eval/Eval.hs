module Eval.Eval (eval) where

import Prettyprinter

import Data.List (find)
import Syntax.Terms
import Eval.TermSubstitution
import Utils
import Pretty

type EvalM a = Either Error a

lookupCase :: XtorName -> [Case a] -> EvalM (Case a)
lookupCase xt cases = case find (\MkCase { case_name } -> xt == case_name) cases of
  Just pmcase -> Right pmcase
  Nothing -> Left $ EvalError $ unlines ["Error during evaluation. The xtor: "
                                        , unXtorName xt
                                        , "doesn't occur in match."
                                        ]

lengthXtorArgs :: XtorArgs a -> Twice Int
lengthXtorArgs MkXtorArgs { prdArgs, cnsArgs } = Twice (length prdArgs) (length cnsArgs)

checkArgs :: Pretty a => Command a -> Twice [a] -> XtorArgs a -> EvalM ()
checkArgs cmd argTypes args =
  if fmap length argTypes == lengthXtorArgs args
  then return ()
  else Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                           "\"\nArgument lengths don't coincide.")

-- | Returns Nothing if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalOneStep :: Pretty a => Command a -> EvalM (Maybe (Command a))
evalOneStep Done = return Nothing
evalOneStep (Print _) = return Nothing
evalOneStep cmd@(Apply (XtorCall PrdRep xt args) (Match CnsRep _ cases)) = do
  (MkCase _ argTypes cmd') <- lookupCase xt cases
  checkArgs cmd argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalOneStep cmd@(Apply (Match PrdRep _ cases) (XtorCall CnsRep xt args)) = do
  (MkCase _ argTypes cmd') <- lookupCase xt cases
  checkArgs cmd argTypes args
  return (Just (commandOpening args cmd')) --reduction is just opening
evalOneStep (Apply (MuAbs PrdRep _ cmd) cns) = return (Just (commandOpeningSingle CnsRep cns cmd))
evalOneStep (Apply prd (MuAbs CnsRep _ cmd)) = return (Just (commandOpeningSingle PrdRep prd cmd))
-- Error handling
evalOneStep cmd@(Apply _ _) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                          "\"\n Free variable encountered!")


eval :: Pretty a => Command a -> EvalM String
eval cmd = do
  cmd' <- evalOneStep cmd
  case cmd' of
    Nothing -> Right (ppPrint cmd)
    Just cmd' -> eval cmd'

