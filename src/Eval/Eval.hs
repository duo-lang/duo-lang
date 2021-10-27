module Eval.Eval
  ( -- Eval Monad
    EvalOrder(..)
  , EvalM
  , runEval
    -- Helper functions
  , throwEvalError
  , lookupEvalOrder
  ) where

import Control.Monad.Except
import Control.Monad.Reader

import Errors
import Syntax.Program (Environment)

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

-- | An evaluation order is either call-by-value or call-by-name.
data EvalOrder
  = CBV -- ^ Call-by-value
  | CBN -- ^ Call-by-name
  deriving (Show, Eq)

newtype EvalM a = EvalM { unEvalM :: ReaderT (Environment, EvalOrder) (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader (Environment, EvalOrder))

runEval :: EvalM a -> EvalOrder -> Environment -> Either Error a
runEval e evalorder env = runExcept (runReaderT (unEvalM e) (env,evalorder))

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

lookupEvalOrder :: EvalM EvalOrder
lookupEvalOrder = asks snd

