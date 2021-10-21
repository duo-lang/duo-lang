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
import Syntax.Types(EvalOrder)

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

newtype EvalM bs a = EvalM { unEvalM :: ReaderT (Environment bs, EvalOrder) (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader (Environment bs, EvalOrder))

runEval :: EvalM bs a -> EvalOrder -> Environment bs -> Either Error a
runEval e evalorder env = runExcept (runReaderT (unEvalM e) (env,evalorder))

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

lookupEvalOrder :: EvalM bs EvalOrder
lookupEvalOrder = asks snd

