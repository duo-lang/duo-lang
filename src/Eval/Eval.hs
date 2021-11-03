module Eval.Eval
  ( -- Eval Monad
    EvalM
  , runEval
    -- Helper functions
  , throwEvalError
  ) where

import Control.Monad.Except ( MonadError, runExcept, Except )
import Control.Monad.Reader ( ReaderT(..), MonadReader )

import Errors ( Error, throwEvalError )
import Syntax.Program (Environment)

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

newtype EvalM a = EvalM { unEvalM :: ReaderT (Environment, ()) (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader (Environment, ()))

runEval :: EvalM a -> Environment -> Either Error a
runEval e  env = runExcept (runReaderT (unEvalM e) (env,()))



