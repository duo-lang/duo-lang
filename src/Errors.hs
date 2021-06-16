module Errors where

import Control.Monad.Except
import Data.Text

import Utils
----------------------------------------------------------------------------------
-- Errors
----------------------------------------------------------------------------------

data Error
  = ParseError Text
  | GenConstraintsError Text
  | EvalError Text
  | SolveConstraintsError Text
  | TypeAutomatonError Text
  | OtherError Text
  deriving (Show, Eq)

type LocatedError = Located Error

---------------------------------------------------------------------------------------------
-- Throwing errors
---------------------------------------------------------------------------------------------

throwGenError :: MonadError Error m => Text -> m a
throwGenError msg = throwError $ GenConstraintsError msg
