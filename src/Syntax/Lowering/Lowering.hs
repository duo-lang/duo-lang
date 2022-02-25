module Syntax.Lowering.Lowering
  ( LoweringError(..)
  , LowerM
  , runLowerM
  ) where

import Control.Monad.Except

import Errors

newtype LowerM a = MkLowerM { unLowerM :: Except Error a }
  deriving (Functor, Applicative, Monad, MonadError Error)

runLowerM :: LowerM a -> Either Error a
runLowerM m = runExcept (unLowerM m)