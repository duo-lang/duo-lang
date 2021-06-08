module Eval.Eval
  ( -- Eval Monad
    EvalOrder(..)
  , EvalM
  , runEval
    -- Helper functions
  , throwEvalError
  , lookupDef
  , lookupPrd
  , lookupCns
  , lookupEvalOrder
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text as T

import Pretty.Pretty
import Syntax.ATerms
import Syntax.Program (Environment(..))
import Syntax.STerms
import Syntax.Types
import Utils

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

-- | An evaluation order is either call-by-value or call-by-name.
data EvalOrder
  = CBV -- ^ Call-by-value
  | CBN -- ^ Call-by-name
  deriving (Show, Eq)

newtype EvalM bs a = EvalM { unEvalM :: ReaderT (EvalOrder, Environment bs) (Except Error) a }
  deriving (Functor, Applicative, Monad, MonadError Error, MonadReader (EvalOrder, Environment bs))

runEval :: EvalM bs a -> EvalOrder -> Environment bs -> Either Error a
runEval e evalorder env = runExcept (runReaderT (unEvalM e) (evalorder, env))

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

throwEvalError :: [Text] -> EvalM bs a
throwEvalError = throwError . EvalError . T.unlines

lookupDef :: FreeVarName -> EvalM bs (ATerm () bs, TypeScheme Pos)
lookupDef fv = do
  env <- asks snd
  case M.lookup fv (defEnv env) of
    Nothing -> throwEvalError ["Unbound free variable " <> ppPrint fv <> " not contained in environment."]
    Just res -> return res

lookupPrd :: FreeVarName -> EvalM bs (STerm Prd () bs, TypeScheme Pos)
lookupPrd fv = do
  env <- asks snd
  case M.lookup fv (prdEnv env) of
    Nothing -> throwEvalError ["Unbound free variable " <> ppPrint fv <> " not contained in environment."]
    Just res -> return res

lookupCns :: FreeVarName -> EvalM bs (STerm Cns () bs, TypeScheme Neg)
lookupCns fv = do
  env <- asks snd
  case M.lookup fv (cnsEnv env) of
    Nothing -> throwEvalError ["Unbound free variable " <> ppPrint fv <> " not contained in environment."]
    Just res -> return res

lookupEvalOrder :: EvalM bs EvalOrder
lookupEvalOrder = asks fst

