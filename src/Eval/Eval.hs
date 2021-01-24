module Eval.Eval
  ( EvalOrder(..)
  , runEval
  , eval
  , evalSteps
  ) where

import Prettyprinter
import Control.Monad.Reader
import Control.Monad.Except
import Data.List (find)
import Syntax.STerms
import Eval.Substitution
import Utils
import Pretty.Pretty

data EvalOrder = CBV | CBN

type EvalM a = (ReaderT EvalOrder (Except Error)) a

runEval :: EvalM a -> EvalOrder -> Either Error a
runEval e evalorder = runExcept (runReaderT e evalorder)

lookupCase :: XtorName -> [SCase a] -> EvalM (SCase a)
lookupCase xt cases = case find (\MkSCase { scase_name } -> xt == scase_name) cases of
  Just pmcase -> return pmcase
  Nothing -> throwError $ EvalError $ unlines ["Error during evaluation. The xtor: "
                                              , unXtorName xt
                                              , "doesn't occur in match."
                                              ]

lengthXtorArgs :: XtorArgs a -> Twice Int
lengthXtorArgs MkXtorArgs { prdArgs, cnsArgs } = Twice (length prdArgs) (length cnsArgs)

checkArgs :: Pretty a => Command a -> Twice [a] -> XtorArgs a -> EvalM ()
checkArgs cmd argTypes args =
  if fmap length argTypes == lengthXtorArgs args
  then return ()
  else throwError $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                               "\"\nArgument lengths don't coincide.")

-- | Returns Nothing if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalOneStep :: Pretty a => Command a -> EvalM (Maybe (Command a))
evalOneStep Done = return Nothing
evalOneStep (Print _) = return Nothing
evalOneStep cmd@(Apply (XtorCall PrdRep xt args) (XMatch CnsRep _ cases)) = do
  (MkSCase _ argTypes cmd') <- lookupCase xt cases
  checkArgs cmd argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalOneStep cmd@(Apply (XMatch PrdRep _ cases) (XtorCall CnsRep xt args)) = do
  (MkSCase _ argTypes cmd') <- lookupCase xt cases
  checkArgs cmd argTypes args
  return (Just (commandOpening args cmd')) --reduction is just opening
evalOneStep (Apply prd@(MuAbs PrdRep _ cmd) cns@(MuAbs CnsRep _ cmd')) = do
  evalOrder <- ask
  case evalOrder of
    CBV -> return (Just (commandOpeningSingle CnsRep cns cmd))
    CBN -> return (Just (commandOpeningSingle PrdRep prd cmd'))
evalOneStep (Apply (MuAbs PrdRep _ cmd) cns) = return (Just (commandOpeningSingle CnsRep cns cmd))
evalOneStep (Apply prd (MuAbs CnsRep _ cmd)) = return (Just (commandOpeningSingle PrdRep prd cmd))
-- Error handling
evalOneStep cmd@(Apply _ _) = throwError $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                      "\"\n Free variable encountered!")

-- | Return just thef final evaluation result
eval :: Pretty a => Command a -> EvalM (Command a)
eval cmd = do
  cmd' <- evalOneStep cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> eval cmd'

-- | Return all intermediate evaluation results
evalSteps :: Pretty a => Command a -> EvalM [Command a]
evalSteps cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: Pretty a => [Command a] -> Command a -> EvalM [Command a]
    evalSteps' cmds cmd = do
      cmd' <- evalOneStep cmd
      case cmd' of
        Nothing -> return cmds
        Just cmd' -> evalSteps' (cmds ++ [cmd']) cmd'

