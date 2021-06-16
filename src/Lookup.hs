module Lookup
  ( lookupDef
  , lookupPrd
  , lookupCns
  , withPrd
  , withCns
  , withDef
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import qualified Data.Map as M

import Errors
import Pretty.Pretty
import Syntax.CommonTerm
import Syntax.STerms
import Syntax.ATerms
import Syntax.Types
import Syntax.Program

type Foo bs a m = (MonadError Error m, MonadReader (Environment bs, a) m)

---------------------------------------------------------------------------------
-- Lookup
---------------------------------------------------------------------------------

lookupDef :: (MonadError Error m, MonadReader (Environment bs, a) m)
          => FreeVarName -> m (ATerm () bs, TypeScheme Pos)
lookupDef fv = do
  env <- asks fst
  case M.lookup fv (defEnv env) of
    Nothing -> throwEvalError ["Unbound free variable " <> ppPrint fv <> " not contained in environment."]
    Just res -> return res

lookupPrd :: (MonadError Error m, MonadReader (Environment bs, a) m)
          => FreeVarName -> m (STerm Prd () bs, TypeScheme Pos)
lookupPrd fv = do
  env <- asks fst
  case M.lookup fv (prdEnv env) of
    Nothing -> throwEvalError ["Unbound free variable " <> ppPrint fv <> " not contained in environment."]
    Just res -> return res

lookupCns :: (MonadError Error m, MonadReader (Environment bs, a) m)
          => FreeVarName -> m (STerm Cns () bs, TypeScheme Neg)
lookupCns fv = do
  env <- asks fst
  case M.lookup fv (cnsEnv env) of
    Nothing -> throwEvalError ["Unbound free variable " <> ppPrint fv <> " not contained in environment."]
    Just res -> return res

---------------------------------------------------------------------------------
-- ChangeEnvironment
---------------------------------------------------------------------------------

withPrd :: Foo bs a m
           => FreeVarName -> STerm Prd () bs -> TypeScheme Pos -> m b-> m b
withPrd fv tm tys m = do
  let modifyEnv (env@Environment { prdEnv }, rest) =
        (env { prdEnv = M.insert fv (tm,tys) prdEnv }, rest)
  local modifyEnv m

withCns :: Foo bs a m
           => FreeVarName -> STerm Cns () bs -> TypeScheme Neg -> m b -> m b
withCns fv tm tys m = do
  let modifyEnv (env@Environment { cnsEnv }, rest) =
        (env { cnsEnv = M.insert fv (tm,tys) cnsEnv }, rest)
  local modifyEnv m

withDef :: Foo bs a m
           => FreeVarName -> ATerm () bs -> TypeScheme Pos -> m b -> m b
withDef fv tm tys m = do
  let modifyEnv (env@Environment { defEnv }, rest) =
        (env { defEnv = M.insert fv (tm,tys) defEnv }, rest)
  local modifyEnv m
