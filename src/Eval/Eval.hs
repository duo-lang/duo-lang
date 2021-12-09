module Eval.Eval
  ( eval
  , evalSteps
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Data.List (find)
import Data.Text qualified as T
import Text.Read (readMaybe)

import Errors
import Lookup
import Pretty.Pretty
import Pretty.Terms ()
import Syntax.Program (Environment)
import Syntax.Kinds (CallingConvention(..), Kind(..))
import Syntax.CommonTerm
import Syntax.Terms

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

newtype EvalM a = EvalM { unEvalM :: ReaderT (Environment Compiled, ()) (ExceptT Error IO) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader (Environment Compiled, ()), MonadIO)

runEval :: EvalM a -> Environment Compiled -> IO (Either Error a)
runEval e env = runExceptT (runReaderT (unEvalM e) (env, ()))

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

lookupMatchCase :: XtorName -> [CmdCase Compiled] -> EvalM (CmdCase Compiled)
lookupMatchCase xt cases = case find (\MkCmdCase { cmdcase_name } -> xt == cmdcase_name) cases of
  Just pmcase -> return pmcase
  Nothing -> throwEvalError ["Error during evaluation. The xtor: "
                            , unXtorName xt
                            , "doesn't occur in match."
                            ]

checkArgs :: Command Compiled -> [(PrdCns,a)] -> Substitution Compiled -> EvalM ()
checkArgs _md [] [] = return ()
checkArgs cmd ((Prd,_):rest1) (PrdTerm _:rest2) = checkArgs cmd rest1 rest2
checkArgs cmd ((Cns,_):rest1) (CnsTerm _:rest2) = checkArgs cmd rest1 rest2
checkArgs cmd _ _ = throwEvalError [ "Error during evaluation of:"
                                   , ppPrint cmd
                                   , "Argument lengths don't coincide."
                                   ]


convertInt :: Int -> Term Prd Compiled
convertInt 0 = XtorCall () PrdRep (MkXtorName Nominal "Z") []
convertInt n = XtorCall () PrdRep (MkXtorName Nominal "S") [PrdTerm $ convertInt (n-1)]


readInt :: IO (Term Prd Compiled)
readInt = do
  input <- getLine
  case readMaybe input of
    Nothing -> putStrLn "Incorrect input" >> readInt
    Just i -> pure (convertInt i)



---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

-- | Returns Notihng if command was in normal form, Just cmd' if cmd reduces to cmd' in one step
evalTermOnce :: Command Compiled -> EvalM (Maybe (Command Compiled))
evalTermOnce (Done _) = return Nothing
evalTermOnce (Print _ prd cmd) = do
  liftIO $ ppPrintIO prd
  return (Just cmd)
evalTermOnce (Read _ cns) = do
  tm <- liftIO $ readInt
  return (Just (Apply () (Just (MonoKind CBV)) tm cns))
evalTermOnce (Apply _ Nothing _ _) = throwEvalError ["Tried to evaluate command which was not correctly kind annotated (Nothing)"]
evalTermOnce (Apply _ (Just (KindVar _)) _ _) = throwEvalError ["Tried to evaluate command which was not correctly kind annotated (KindVar)"]
evalTermOnce (Apply _ (Just (MonoKind cc)) prd cns) = evalApplyOnce cc prd cns

evalApplyOnce :: CallingConvention -> Term Prd Compiled -> Term Cns Compiled -> EvalM  (Maybe (Command Compiled))
-- Free variables have to be looked up in the environment.
evalApplyOnce eo (FreeVar _ PrdRep fv) cns = do
  (prd,_) <- lookupTerm PrdRep fv
  return (Just (Apply () (Just (MonoKind eo)) prd cns))
evalApplyOnce eo prd (FreeVar _ CnsRep fv) = do
  (cns,_) <- lookupTerm CnsRep fv
  return (Just (Apply () (Just (MonoKind eo)) prd cns))
-- (Co-)Pattern matches are evaluated using the ordinary pattern matching rules.
evalApplyOnce _ prd@(XtorCall _ PrdRep xt args) cns@(XMatch _ CnsRep _ cases) = do
  (MkCmdCase _ _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply () Nothing prd cns) argTypes args
  return (Just  (commandOpening args cmd')) --reduction is just opening
evalApplyOnce _ prd@(XMatch _ PrdRep _ cases) cns@(XtorCall _ CnsRep xt args) = do
  (MkCmdCase _ _ argTypes cmd') <- lookupMatchCase xt cases
  checkArgs (Apply () Nothing prd cns) argTypes args
  return (Just (commandOpening args cmd')) --reduction is just opening
-- Mu abstractions have to be evaluated while taking care of evaluation order.
evalApplyOnce CBV (MuAbs _ PrdRep _ cmd) cns@(MuAbs _ CnsRep _ _) = 
  return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce CBN prd@(MuAbs _ PrdRep _ _) (MuAbs _ CnsRep _ cmd) = 
  return (Just (commandOpening [PrdTerm prd] cmd))
evalApplyOnce _ (MuAbs _ PrdRep _ cmd) cns = return (Just (commandOpening [CnsTerm cns] cmd))
evalApplyOnce _ prd (MuAbs _ CnsRep _ cmd) = return (Just (commandOpening [PrdTerm prd] cmd))
-- Bound variables should not occur at the toplevel during evaluation.
evalApplyOnce _ (BoundVar _ PrdRep i) _ = throwEvalError ["Found bound variable during evaluation. Index: " <> T.pack (show i)]
evalApplyOnce _ _ (BoundVar _ CnsRep i) = throwEvalError [ "Found bound variable during evaluation. Index: " <> T.pack (show i)]
-- Match applied to Match, or Xtor to Xtor can't evaluate
evalApplyOnce _ XMatch{} XMatch{} = throwEvalError ["Cannot evaluate match applied to match"]
evalApplyOnce _ XtorCall{} XtorCall{} = throwEvalError ["Cannot evaluate constructor applied to destructor"]
evalApplyOnce _ _ _ = throwEvalError ["Cannot evaluate, probably an asymmetric term..."]


-- | Return just the final evaluation result
evalM :: Command Compiled -> EvalM (Command Compiled)
evalM cmd = do
  cmd' <- evalTermOnce cmd
  case cmd' of
    Nothing -> return cmd
    Just cmd' -> evalM cmd'

-- | Return all intermediate evaluation results
evalStepsM :: Command Compiled -> EvalM [Command Compiled]
evalStepsM cmd = evalSteps' [cmd] cmd
  where
    evalSteps' :: [Command Compiled] -> Command Compiled -> EvalM [Command Compiled]
    evalSteps' cmds cmd = do
      cmd' <- evalTermOnce cmd
      case cmd' of
        Nothing -> return cmds
        Just cmd' -> evalSteps' (cmds ++ [cmd']) cmd'

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

eval :: Command Compiled -> Environment Compiled -> IO (Either Error (Command Compiled))
eval cmd env = runEval (evalM cmd) env

evalSteps :: Command Compiled -> Environment Compiled -> IO (Either Error [Command Compiled])
evalSteps cmd env = runEval (evalStepsM cmd) env