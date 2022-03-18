module Eval.Definition where

import Control.Monad.Except
import Control.Monad.Reader
import Data.List (find)
import Text.Read (readMaybe)

import Errors
import Pretty.Pretty
import Pretty.Terms ()
import Syntax.Environment (Environment)
import Syntax.Common
import Syntax.AST.Terms

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
convertInt 0 = Xtor () PrdRep Nominal (MkXtorName "Z") []
convertInt n = Xtor () PrdRep Nominal (MkXtorName "S") [PrdTerm $ convertInt (n-1)]


readInt :: IO (Term Prd Compiled)
readInt = do
  putStrLn "Enter a positive integer:"
  input <- getLine
  case readMaybe input of
    Nothing        -> putStrLn "Incorrect input." >> readInt
    Just i | i < 0 -> putStrLn "Incorrect input." >> readInt
    Just i         -> pure (convertInt i)
