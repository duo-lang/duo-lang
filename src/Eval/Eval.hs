module Eval.Eval
  ( EvalOrder(..)
  , EvalM
  , runEval
  ) where

import Control.Monad.Reader
import Control.Monad.Except
import Data.List (find)
import qualified Data.Map as M (lookup)
import Data.Maybe (fromJust)
import Prettyprinter

import Pretty.Pretty
import Syntax.Program (Environment, defEnv, prdEnv, cnsEnv)


import Utils


data EvalOrder = CBV | CBN

type EvalM a = ReaderT (EvalOrder, Environment) (Except Error) a

runEval :: EvalM a -> EvalOrder -> Environment -> Either Error a
runEval e evalorder env = runExcept (runReaderT e (evalorder, env))

