module Eval.Definition where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Map (Map)
import Data.Map qualified as M
import Data.List (find)
import Text.Read (readMaybe)

import Errors
import Pretty.Pretty
import Pretty.Terms ()
import Syntax.Common
import Syntax.Core.Terms
import Utils

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

type EvalEnv = (Map FreeVarName (Term Prd), Map FreeVarName (Term Cns), Map FreeVarName Command)

newtype EvalM a = EvalM { unEvalM :: ReaderT EvalEnv (ExceptT Error IO) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader EvalEnv, MonadIO)

runEval :: EvalM a -> EvalEnv -> IO (Either Error a)
runEval e env = runExceptT (runReaderT (unEvalM e) env)

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

lookupMatchCase :: XtorName -> [CmdCase] -> EvalM CmdCase
lookupMatchCase xt cases = case find (\MkCmdCase { cmdcase_pat = XtorPat _ xt' _ } -> xt == xt') cases of
  Just pmcase -> return pmcase
  Nothing -> throwEvalError ["Error during evaluation. The xtor: "
                            , unXtorName xt
                            , "doesn't occur in match."
                            ]

checkArgs :: Command -> [(PrdCns,a)] -> Substitution -> EvalM ()
checkArgs _md [] [] = return ()
checkArgs cmd ((Prd,_):rest1) (PrdTerm _:rest2) = checkArgs cmd rest1 rest2
checkArgs cmd ((Cns,_):rest1) (CnsTerm _:rest2) = checkArgs cmd rest1 rest2
checkArgs cmd _ _ = throwEvalError [ "Error during evaluation of:"
                                   ,  ppPrint cmd
                                   , "Argument lengths don't coincide."
                                   ]


convertInt :: Int -> Term Prd
convertInt 0 = Xtor defaultLoc XtorAnnotOrig PrdRep Nominal (MkXtorName "Z") []
convertInt n = Xtor defaultLoc XtorAnnotOrig PrdRep Nominal (MkXtorName "S") [PrdTerm $ convertInt (n-1)]


readInt :: IO (Term Prd)
readInt = do
  putStrLn "Enter a positive integer:"
  input <- getLine
  case readMaybe input of
    Nothing        -> putStrLn "Incorrect input." >> readInt
    Just i | i < 0 -> putStrLn "Incorrect input." >> readInt
    Just i         -> pure (convertInt i)

lookupCommand :: FreeVarName -> EvalM Command
lookupCommand fv = do
  (_,_,env) <- ask
  case M.lookup fv env of
    Nothing -> throwEvalError ["Consumer " <> ppPrint fv <> " not in environment."]
    Just cmd -> pure cmd

lookupTerm :: PrdCnsRep pc -> FreeVarName -> EvalM (Term pc)
lookupTerm PrdRep fv = do
  (env,_,_) <- ask
  case M.lookup fv env of
    Nothing -> throwEvalError ["Producer " <> ppPrint fv <> " not in environment."]
    Just prd -> pure prd
lookupTerm CnsRep fv = do
  (_,env,_) <- ask
  case M.lookup fv env of
    Nothing -> throwEvalError ["Consumer " <> ppPrint fv <> " not in environment."]
    Just prd -> pure prd