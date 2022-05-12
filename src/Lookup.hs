module Lookup
  ( PrdCnsToPol
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
import Data.Map (Map)
import Data.Map qualified as M

import Driver.Environment (Environment(..), emptyEnvironment)
import Errors
import Pretty.Pretty
import Pretty.Common ()
import Syntax.Common
import Syntax.AST.Terms qualified as AST
import Syntax.Common.TypesPol
import Utils

---------------------------------------------------------------------------------
-- We define functions which work for every Monad which implements:
-- (1) MonadError Error
-- (2) MonadReader (Map ModuleName Environment ph, a)
---------------------------------------------------------------------------------

type EnvReader a m = (MonadError Error m, MonadReader (Map ModuleName Environment, a) m)

---------------------------------------------------------------------------------
-- Lookup Terms
---------------------------------------------------------------------------------

findFirstM :: forall a m res. EnvReader a m
           => (Environment -> Maybe res)
           -> Error
           -> m (ModuleName, res)
findFirstM f err = asks fst >>= \env -> go (M.toList env)
  where
    go :: [(ModuleName, Environment)] -> m (ModuleName, res)
    go [] = throwError err
    go ((mn,env):envs) =
      case f env of
        Just res -> pure (mn,res)
        Nothing -> go envs

-- | Lookup the term and the type of a term bound in the environment.
lookupTerm :: EnvReader a m
           => PrdCnsRep pc -> FreeVarName -> m (AST.Term pc, TypeScheme (PrdCnsToPol pc))
lookupTerm PrdRep fv = do
  env <- asks fst
  let err = OtherError Nothing ("Unbound free producer variable " <> ppPrint fv <> " is not contained in environment.\n" <> (ppPrint $ M.keys env))
  let f env = case M.lookup fv (prdEnv env) of
                       Nothing -> Nothing
                       Just (res1,_,res2) -> Just (res1,res2)
  snd <$> findFirstM f err
lookupTerm CnsRep fv = do
  let err = OtherError Nothing ("Unbound free consumer variable " <> ppPrint fv <> " is not contained in environment.")
  let f env = case M.lookup fv (cnsEnv env) of
                       Nothing -> Nothing
                       Just (res1,_,res2) -> return (res1,res2)
  snd <$> findFirstM f err

---------------------------------------------------------------------------------
-- Lookup Commands
---------------------------------------------------------------------------------

-- | Lookup a command in the environment.
lookupCommand :: EnvReader a m => FreeVarName -> m AST.Command
lookupCommand fv = do
  let err = OtherError Nothing ("Unbound free command variable " <> ppPrint fv <> " is not contained in environment.")
  let f env = case M.lookup fv (cmdEnv env) of
                     Nothing -> Nothing
                     Just (res, _) -> return res
  snd <$> findFirstM f err

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
      typeContainsXtor NominalDecl { data_xtors } | or (containsXtor <$> fst data_xtors) = True
                                                  | otherwise = False
  let err = OtherError Nothing ("Constructor/Destructor " <> ppPrint xt <> " is not contained in program.")
  let f env = find typeContainsXtor (fmap snd (declEnv env))
  snd <$> findFirstM f err

-- | Find the type declaration belonging to a given TypeName.
lookupTypeName :: EnvReader a m
               => RnTypeName -> m DataDecl
lookupTypeName tn = do
  let err = OtherError Nothing ("Type name " <> unTypeName (rnTnName tn) <> " not found in environment")
  let f env = find (\NominalDecl{..} -> data_name == tn) (fmap snd (declEnv env))
  snd <$> findFirstM f err

-- | Find the XtorSig belonging to a given XtorName.
lookupXtorSig :: EnvReader a m
              => XtorName -> PolarityRep pol -> m (XtorSig pol)
lookupXtorSig xtn PosRep = do
  decl <- lookupDataDecl xtn
  case find ( \MkXtorSig{..} -> sig_name == xtn ) (fst (data_xtors decl)) of
    Just xts -> return xts
    Nothing -> throwOtherError ["XtorName " <> unXtorName xtn <> " not found in declaration of type " <> unTypeName (rnTnName (data_name decl))]
lookupXtorSig xtn NegRep = do
  decl <- lookupDataDecl xtn
  case find ( \MkXtorSig{..} -> sig_name == xtn ) (snd (data_xtors decl)) of
    Just xts -> return xts
    Nothing -> throwOtherError ["XtorName " <> unXtorName xtn <> " not found in declaration of type " <> unTypeName (rnTnName (data_name decl))]

---------------------------------------------------------------------------------
-- Run a computation in a locally changed environment.
---------------------------------------------------------------------------------

withTerm :: forall a m b pc. EnvReader a m
         => ModuleName -> PrdCnsRep pc -> FreeVarName -> AST.Term pc -> Loc -> TypeScheme (PrdCnsToPol pc)
         -> (m b -> m b)
withTerm mn PrdRep fv tm loc tys action = do
  let modifyEnv :: Environment -> Environment
      modifyEnv env@MkEnvironment { prdEnv } =
        env { prdEnv = M.insert fv (tm,loc,tys) prdEnv }
  let modifyEnvMap :: (Map ModuleName Environment, a) -> (Map ModuleName Environment, a)
      modifyEnvMap (map, rest) =
        case M.lookup mn map of
          Nothing -> (M.insert mn (modifyEnv emptyEnvironment) map, rest)
          Just _  -> (M.adjust modifyEnv mn map, rest)
  local modifyEnvMap action
withTerm mn CnsRep fv tm loc tys action = do
  let modifyEnv :: Environment -> Environment
      modifyEnv env@MkEnvironment { cnsEnv } =
        env { cnsEnv = M.insert fv (tm,loc,tys) cnsEnv }
  let modifyEnvMap :: (Map ModuleName Environment, a) -> (Map ModuleName Environment, a)
      modifyEnvMap (map, rest) =
        case M.lookup mn map of
          Nothing ->  (M.insert mn (modifyEnv emptyEnvironment) map, rest)
          Just _  -> (M.adjust modifyEnv mn map, rest)
  local modifyEnvMap action

