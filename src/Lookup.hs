module Lookup
  ( HasEnv
  , getEnv
  , PrdCnsToPol
  , prdCnsToPol
  , lookupTerm
  , lookupCommand
  , lookupDataDecl
  , lookupTypeName
  , lookupXtorSig
  , withTerm
    ) where

import Control.Monad.Except
import Control.Monad.Reader
import Data.List
import Data.Map qualified as M


import Errors
import Pretty.Pretty
import Syntax.Common
import Syntax.AST.Terms
import Syntax.AST.Types
import Syntax.AST.Program
import Utils

---------------------------------------------------------------------------------
-- We define functions which work for every Monad which implements:
-- (1) MonadError Error
-- (2) HasEnv
---------------------------------------------------------------------------------

class HasEnv m where
  getEnv :: m (Environment 'Inferred)

type EnvReader a m = (MonadError Error m, HasEnv m)

---------------------------------------------------------------------------------
-- Lookup Terms
---------------------------------------------------------------------------------

-- | Lookup the term and the type of a term bound in the environment.
lookupTerm :: EnvReader a m
           => PrdCnsRep pc -> FreeVarName -> m (Term pc 'Inferred, TypeScheme (PrdCnsToPol pc))
lookupTerm PrdRep fv = do
  env <- getEnv
  case M.lookup fv (prdEnv env) of
    Nothing -> throwOtherError ["Unbound free variable " <> ppPrint fv <> " is not contained in environment."]
    Just (res1,_,res2) -> return (res1,res2)
lookupTerm CnsRep fv = do
  env <- getEnv
  case M.lookup fv (cnsEnv env) of
    Nothing -> throwOtherError ["Unbound free variable " <> ppPrint fv <> " is not contained in the environment."]
    Just (res1,_,res2) -> return (res1,res2)

---------------------------------------------------------------------------------
-- Lookup Commands
---------------------------------------------------------------------------------

-- | Lookup a command in the environment.
lookupCommand :: EnvReader a m => FreeVarName -> m (Command 'Inferred)
lookupCommand fv = do
  env <- getEnv
  case M.lookup fv (cmdEnv env) of
    Nothing -> throwOtherError ["Unbound free variable " <> ppPrint fv <> " is not contained in environment."]
    Just (res, _) -> return res

---------------------------------------------------------------------------------
-- Lookup information about type declarations
---------------------------------------------------------------------------------

-- | Find the type declaration belonging to a given Xtor Name.
lookupDataDecl :: EnvReader a m
               => XtorName -> m DataDecl
lookupDataDecl xt = do
  let containsXtor :: XtorSig Pos -> Bool
      containsXtor sig = sig_name sig == xt
  let typeContainsXtor :: DataDecl -> Bool
      typeContainsXtor NominalDecl { data_xtors } | or (containsXtor <$> (fst data_xtors)) = True
                                                  | otherwise = False
  env <- fmap snd . declEnv <$> getEnv
  case find typeContainsXtor env of
    Nothing -> throwOtherError ["Constructor/Destructor " <> ppPrint xt <> " is not contained in program."]
    Just decl -> return decl

-- | Find the type declaration belonging to a given TypeName.
lookupTypeName :: EnvReader a m
               => TypeName -> m DataDecl
lookupTypeName tn = do
  env <- fmap snd . declEnv <$> getEnv
  case find (\NominalDecl{..} -> data_name == tn) env of
    Just decl -> return decl
    Nothing -> throwOtherError ["Type name " <> unTypeName tn <> " not found in environment"]

-- | Find the XtorSig belonging to a given XtorName.
lookupXtorSig :: EnvReader a m
              => XtorName -> PolarityRep pol -> m (XtorSig pol)
lookupXtorSig xtn PosRep = do
  decl <- lookupDataDecl xtn
  case find ( \MkXtorSig{..} -> sig_name == xtn ) (fst (data_xtors decl)) of
    Just xts -> return xts
    Nothing -> throwOtherError ["XtorName " <> unXtorName xtn <> " not found in declaration of type " <> unTypeName (data_name decl)]
lookupXtorSig xtn NegRep = do
  decl <- lookupDataDecl xtn
  case find ( \MkXtorSig{..} -> sig_name == xtn ) (snd (data_xtors decl)) of
    Just xts -> return xts
    Nothing -> throwOtherError ["XtorName " <> unXtorName xtn <> " not found in declaration of type " <> unTypeName (data_name decl)]

---------------------------------------------------------------------------------
-- Run a computation in a locally changed environment.
---------------------------------------------------------------------------------

withTerm :: (MonadError Error m, MonadReader (Environment 'Inferred, a) m)
         => PrdCnsRep pc -> FreeVarName -> Term pc 'Inferred -> Loc -> TypeScheme (PrdCnsToPol pc)
         -> (m b -> m b)
withTerm PrdRep fv tm loc tys m = do
  let modifyEnv (env@MkEnvironment { prdEnv }, rest) =
        (env { prdEnv = M.insert fv (tm,loc,tys) prdEnv }, rest)
  local modifyEnv m
withTerm CnsRep fv tm loc tys m = do
  let modifyEnv (env@MkEnvironment { cnsEnv }, rest) =
        (env { cnsEnv = M.insert fv (tm,loc,tys) cnsEnv }, rest)
  local modifyEnv m
