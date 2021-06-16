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

newtype EvalM bs a = EvalM { unEvalM :: ReaderT (Environment bs, EvalOrder) (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader (Environment bs, EvalOrder))

runEval :: EvalM bs a -> EvalOrder -> Environment bs -> Either Error a
runEval e evalorder env = runExcept (runReaderT (unEvalM e) (env,evalorder))

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

lookupEvalOrder :: EvalM bs EvalOrder
lookupEvalOrder = asks snd

