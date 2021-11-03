module Lookup
  ( PrdCnsToPol
  , prdCnsToPol
  , lookupSTerm
  , lookupATerm
  , lookupDataDecl
  , lookupTypeName
  , lookupXtorSig
  , withSTerm
  , withATerm
  , annotateKind
  , getKind
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Data.List
import qualified Data.Map as M


import Errors
import Pretty.Pretty
import Syntax.CommonTerm
import Syntax.STerms
import Syntax.ATerms
import Syntax.Types
import Syntax.Kinds
import Syntax.Program
import Utils

---------------------------------------------------------------------------------
-- We define functions which work for every Monad which implements:
-- (1) MonadError Error
-- (2) MonadReader (Environment bs, a)
---------------------------------------------------------------------------------

type EnvReader bs a m = (MonadError Error m, MonadReader (Environment, a) m)

---------------------------------------------------------------------------------
-- Lookup Terms
---------------------------------------------------------------------------------

-- | Lookup the term and the type of a asymmetric term bound in the environment.
lookupATerm :: EnvReader bs a m
            => FreeVarName -> m (ATerm Inferred, TypeScheme Pos)
lookupATerm fv = do
  env <- asks fst
  case M.lookup fv (defEnv env) of
    Nothing -> throwOtherError ["Unbound free variable " <> ppPrint fv <> " not contained in the environment."]
    Just (res1,_,res2) -> return (res1, res2)

-- | Lookup the term and the type of a symmetric term bound in the environment.
lookupSTerm :: EnvReader bs a m
            => PrdCnsRep pc -> FreeVarName -> m (STerm pc Inferred, TypeScheme (PrdCnsToPol pc))
lookupSTerm PrdRep fv = do
  env <- asks fst
  case M.lookup fv (prdEnv env) of
    Nothing -> throwOtherError ["Unbound free variable " <> ppPrint fv <> " is not contained in environment."]
    Just (res1,_,res2) -> return (res1,res2)
lookupSTerm CnsRep fv = do
  env <- asks fst
  case M.lookup fv (cnsEnv env) of
    Nothing -> throwOtherError ["Unbound free variable " <> ppPrint fv <> " is not contained in the environment."]
    Just (res1,_,res2) -> return (res1,res2)

---------------------------------------------------------------------------------
-- Lookup information about type declarations
---------------------------------------------------------------------------------

-- | Find the type declaration belonging to a given Xtor Name.
lookupDataDecl :: EnvReader bs a m
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
lookupTypeName :: EnvReader bs a m
               => TypeName -> m DataDecl
lookupTypeName tn = do
  env <- asks $ fmap snd . declEnv . fst
  case find (\NominalDecl{..} -> data_name == tn) env of
    Just decl -> return decl
    Nothing -> throwOtherError ["Type name " <> unTypeName tn <> " not found in environment"]

-- | Find the XtorSig belonging to a given XtorName.
lookupXtorSig :: EnvReader bs a m
              => XtorName -> PolarityRep pol -> m (XtorSig pol)
lookupXtorSig xtn pol = do
  decl <- lookupDataDecl xtn
  case find ( \MkXtorSig{..} -> sig_name == xtn ) (data_xtors decl pol) of
    Just xts -> return xts
    Nothing -> throwOtherError ["XtorName " <> unXtorName xtn <> " not found in declaration of type " <> unTypeName (data_name decl)]

---------------------------------------------------------------------------------
-- Run a computation in a locally changed environment.
---------------------------------------------------------------------------------

withSTerm :: EnvReader bs a m
          => PrdCnsRep pc -> FreeVarName -> STerm pc Inferred -> Loc -> TypeScheme (PrdCnsToPol pc)
          -> (m b -> m b)
withSTerm PrdRep fv tm loc tys m = do
  let modifyEnv (env@Environment { prdEnv }, rest) =
        (env { prdEnv = M.insert fv (tm,loc,tys) prdEnv }, rest)
  local modifyEnv m
withSTerm CnsRep fv tm loc tys m = do
  let modifyEnv (env@Environment { cnsEnv }, rest) =
        (env { cnsEnv = M.insert fv (tm,loc,tys) cnsEnv }, rest)
  local modifyEnv m

withATerm :: EnvReader bs a m
        => FreeVarName -> ATerm Inferred -> Loc -> TypeScheme Pos
        -> (m b -> m b)
withATerm fv tm loc tys m = do
  let modifyEnv (env@Environment { defEnv }, rest) =
        (env { defEnv = M.insert fv (tm,loc,tys) defEnv }, rest)
  local modifyEnv m

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

annotateXtors :: EnvReader bs a m
              => XtorSig pol -> m (XtorSig pol)
annotateXtors (MkXtorSig xt (MkTypArgs prdArgs cnsArgs)) = do
  prdArgs' <- sequence $ annotateKind <$> prdArgs
  cnsArgs' <- sequence $ annotateKind <$> cnsArgs
  return $ MkXtorSig xt (MkTypArgs prdArgs' cnsArgs')

getKind :: Typ pol -> Kind
getKind (TyVar _ (Just kind) _) = kind
getKind TyData {} = MonoKind CBV
getKind TyCodata {} = MonoKind CBN
getKind (TyNominal _ (Just kind) _ ) = kind
getKind (TySet _ (Just kind) _) = kind
getKind (TyRec _ _ ty) = getKind ty
getKind _              = error "getKind failed: Only apply to fully kind-inferred types!"