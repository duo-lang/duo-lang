module Errors where

import Control.Monad.Except
import Data.Text (Text)
import qualified Data.Text as T

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
-- Throwing errors in a monadic context
---------------------------------------------------------------------------------------------

throwGenError :: MonadError Error m => [Text] -> m a
throwGenError = throwError . GenConstraintsError . T.unlines

throwEvalError :: MonadError Error m => [Text] -> m a
throwEvalError = throwError . EvalError . T.unlines

throwSolverError :: MonadError Error m => [Text] -> m a
throwSolverError = throwError . SolveConstraintsError . T.unlines

throwAutomatonError :: MonadError Error m => [Text] -> m a
throwAutomatonError = throwError . TypeAutomatonError . T.unlines

throwOtherError :: MonadError Error m => [Text] -> m a
throwOtherError = throwError . OtherError . T.unlines
