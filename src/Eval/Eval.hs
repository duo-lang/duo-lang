module Eval.Eval
  ( EvalOrder(..)
  , EvalM
  , runEval
  ) where

import Control.Monad.Reader
import Control.Monad.Except

import Syntax.Program (Environment)
import Utils

data EvalOrder = CBV | CBN

newtype EvalM a = EvalM { unEvalM :: ReaderT (EvalOrder, Environment) (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader (EvalOrder, Environment))

runEval :: EvalM a -> EvalOrder -> Environment -> Either Error a
runEval e evalorder env = runExcept (runReaderT (unEvalM e) (evalorder, env))

