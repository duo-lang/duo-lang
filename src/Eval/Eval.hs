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

newtype EvalM bs a = EvalM { unEvalM :: ReaderT (Environment bs, CallingConvention) (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader (Environment bs, CallingConvention))

runEval :: EvalM bs a -> CallingConvention -> Environment bs -> Either Error a
runEval e evalorder env = runExcept (runReaderT (unEvalM e) (env,evalorder))

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

lookupEvalOrder :: EvalM bs CallingConvention
lookupEvalOrder = asks snd

