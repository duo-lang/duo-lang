module Lookup
  ( PrdCnsToPol
  , prdCnsToPol
  , lookupTerm
  , lookupCommand
  , lookupDataDecl
  , lookupTypeName
  , lookupXtorSig
  , withTerm
  , annotateKind
  , annotateXtors
    ) where

import Control.Monad.Except
import Control.Monad.Reader
import Data.List
import Data.Map qualified as M


import Errors
import Pretty.Pretty
import Syntax.CommonTerm
import Syntax.Terms
import Syntax.Types
import Syntax.Program
import Utils

---------------------------------------------------------------------------------
-- We define functions which work for every Monad which implements:
-- (1) MonadError Error
-- (2) MonadReader (Environment ph, a)
---------------------------------------------------------------------------------

type EnvReader ph a m = (MonadError Error m, MonadReader (Environment ph, a) m)

---------------------------------------------------------------------------------------------
-- Compute the Kind of a Type.
---------------------------------------------------------------------------------------------

-- | Annotate the nominal kinds
annotateKind :: EnvReader bs a m
             => Typ pol -> m (Typ pol)
annotateKind ty@TyVar {} = return ty
annotateKind (TyData rep ref xtors) = do
  xtors' <- sequence $ annotateXtors <$> xtors
  return $ TyData rep ref xtors'
annotateKind (TyCodata rep ref xtors) = do
  xtors' <- sequence $ annotateXtors <$> xtors
  return $ TyCodata rep ref xtors'
annotateKind (TyNominal rep _ tn) = do
  decl <- lookupTypeName tn
  return $ TyNominal rep (Just (data_kind decl)) tn
annotateKind (TySet rep kind tys) = do
  tys' <- sequence $ annotateKind <$> tys
  return (TySet rep kind tys')
annotateKind (TyRec rep tv ty)    = do
  ty' <- annotateKind ty
  return $ TyRec rep tv ty'

annotatePCKind :: EnvReader bs a m
    => PrdCnsType pol -> m (PrdCnsType pol)
annotatePCKind (PrdType ty) = PrdType <$> annotateKind ty
annotatePCKind (CnsType ty) = CnsType <$> annotateKind ty

annotateXtors :: EnvReader bs a m
              => XtorSig pol -> m (XtorSig pol)
annotateXtors (MkXtorSig xt lctxt) = do
  lctxt' <- sequence $ annotatePCKind <$> lctxt
  return $ MkXtorSig xt lctxt'

---------------------------------------------------------------------------------
-- Lookup Terms
---------------------------------------------------------------------------------

-- | Lookup the term and the type of a term bound in the environment.
lookupTerm :: EnvReader ph a m
           => PrdCnsRep pc -> FreeVarName -> m (Term pc ph, TypeScheme (PrdCnsToPol pc))
lookupTerm PrdRep fv = do
  env <- asks fst
  case M.lookup fv (prdEnv env) of
    Nothing -> throwOtherError ["Unbound free variable " <> ppPrint fv <> " is not contained in environment."]
    Just (res1,_,res2) -> return (res1,res2)
lookupTerm CnsRep fv = do
  env <- asks fst
  case M.lookup fv (cnsEnv env) of
    Nothing -> throwOtherError ["Unbound free variable " <> ppPrint fv <> " is not contained in the environment."]
    Just (res1,_,res2) -> return (res1,res2)

---------------------------------------------------------------------------------
-- Lookup Commands
---------------------------------------------------------------------------------

-- | Lookup a command in the environment.
lookupCommand :: EnvReader ph a m => FreeVarName -> m (Command ph)
lookupCommand fv = do
  env <- asks fst
  case M.lookup fv (cmdEnv env) of
    Nothing -> throwOtherError ["Unbound free variable " <> ppPrint fv <> " is not contained in environment."]
    Just (res, _) -> return res

---------------------------------------------------------------------------------
-- Lookup information about type declarations
---------------------------------------------------------------------------------

-- | Find the type declaration belonging to a given Xtor Name.
lookupDataDecl :: EnvReader ph a m
               => XtorName -> m DataDecl
lookupDataDecl xt = do
  let containsXtor :: XtorSig Pos -> Bool
      containsXtor sig = sig_name sig == xt
  let typeContainsXtor :: DataDecl -> Bool
      typeContainsXtor NominalDecl { data_xtors } | or (containsXtor <$> data_xtors PosRep) = True
                                                  | otherwise = False
  env <- asks (((fmap snd) . declEnv) . fst)
  case find typeContainsXtor env of
    Nothing -> throwOtherError ["Constructor/Destructor " <> ppPrint xt <> " is not contained in program."]
    Just decl -> return decl

-- | Find the type declaration belonging to a given TypeName.
lookupTypeName :: EnvReader ph a m
               => TypeName -> m DataDecl
lookupTypeName tn = do
  env <- asks $ fmap snd . declEnv . fst
  case find (\NominalDecl{..} -> data_name == tn) env of
    Just decl -> return decl
    Nothing -> throwOtherError ["Type name " <> unTypeName tn <> " not found in environment"]

-- | Find the XtorSig belonging to a given XtorName.
lookupXtorSig :: EnvReader ph a m
              => XtorName -> PolarityRep pol -> m (XtorSig pol)
lookupXtorSig xtn pol = do
  decl <- lookupDataDecl xtn
  case find ( \MkXtorSig{..} -> sig_name == xtn ) (data_xtors decl pol) of
    Just xts -> return xts
    Nothing -> throwOtherError ["XtorName " <> unXtorName xtn <> " not found in declaration of type " <> unTypeName (data_name decl)]

---------------------------------------------------------------------------------
-- Run a computation in a locally changed environment.
---------------------------------------------------------------------------------

withTerm :: EnvReader ph a m
         => PrdCnsRep pc -> FreeVarName -> Term pc ph -> Loc -> TypeScheme (PrdCnsToPol pc)
         -> (m b -> m b)
withTerm PrdRep fv tm loc tys m = do
  let modifyEnv (env@MkEnvironment { prdEnv }, rest) =
        (env { prdEnv = M.insert fv (tm,loc,tys) prdEnv }, rest)
  local modifyEnv m
withTerm CnsRep fv tm loc tys m = do
  let modifyEnv (env@MkEnvironment { cnsEnv }, rest) =
        (env { cnsEnv = M.insert fv (tm,loc,tys) cnsEnv }, rest)
  local modifyEnv m

