module Eval.Eval
  ( EvalOrder(..)
  , EvalM
  , runEval
  , throwEvalError
  ) where

import Control.Monad.Reader
import Control.Monad.Except

import Syntax.Program (Environment)
import Utils

-- | An evaluation order is either call-by-value or call-by-name.
data EvalOrder
  = CBV -- ^ Call-by-value
  | CBN -- ^ Call-by-name
  deriving (Show, Eq)

newtype EvalM a = EvalM { unEvalM :: ReaderT (EvalOrder, Environment) (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader (EvalOrder, Environment))

runEval :: EvalM a -> EvalOrder -> Environment -> Either Error a
runEval e evalorder env = runExcept (runReaderT (unEvalM e) (evalorder, env))

throwEvalError :: String -> EvalM a
throwEvalError msg = throwError $ EvalError msg
