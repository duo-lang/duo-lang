module Eval.Eval
  ( -- Eval Monad
    EvalM
  , runEval
    -- Helper functions
  , throwEvalError
  , lookupEvalOrder
  ) where

import Control.Monad.Except
import Control.Monad.Reader

import Errors
import Syntax.Program (Environment)
import Syntax.Kinds(CallingConvention)

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

newtype EvalM a = EvalM { unEvalM :: ReaderT (Environment, CallingConvention) (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader (Environment, CallingConvention))

runEval :: EvalM a -> CallingConvention -> Environment -> Either Error a
runEval e evalorder env = runExcept (runReaderT (unEvalM e) (env,evalorder))

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

lookupEvalOrder :: EvalM CallingConvention
lookupEvalOrder = asks snd

