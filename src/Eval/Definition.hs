module Eval.Definition where

import Control.Monad.Except
import Control.Monad.Reader
import Data.List (find)
import Text.Read (readMaybe)

import Driver.Environment (Environment)
import Errors
import Pretty.Pretty
import Pretty.Terms ()
import Syntax.Common
import Syntax.AST.Terms
import Utils

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

newtype EvalM a = EvalM { unEvalM :: ReaderT (Environment, ()) (ExceptT Error IO) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader (Environment, ()), MonadIO)

runEval :: EvalM a -> Environment -> IO (Either Error a)
runEval e env = runExceptT (runReaderT (unEvalM e) (env, ()))

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

lookupMatchCase :: XtorName -> [CmdCase] -> EvalM CmdCase
lookupMatchCase xt cases = case find (\MkCmdCase { cmdcase_name } -> xt == cmdcase_name) cases of
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
                                   , ppPrint cmd
                                   , "Argument lengths don't coincide."
                                   ]


convertInt :: Int -> Term Prd
convertInt 0 = Xtor defaultLoc PrdRep Nothing Nominal (MkXtorName "Z") []
convertInt n = Xtor defaultLoc PrdRep Nothing Nominal (MkXtorName "S") [PrdTerm $ convertInt (n-1)]


readInt :: IO (Term Prd)
readInt = do
  putStrLn "Enter a positive integer:"
  input <- getLine
  case readMaybe input of
    Nothing        -> putStrLn "Incorrect input." >> readInt
    Just i | i < 0 -> putStrLn "Incorrect input." >> readInt
    Just i         -> pure (convertInt i)
