module Lookup
  ( lookupDef
  , lookupPrd
  , lookupCns
  , lookupCase
  , lookupDataDecl
  , lookupXtorSig
  , withPrd
  , withCns
  , withDef
  ) where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Map (Map)
import qualified Data.Map as M
import Data.List

import Errors
import Pretty.Pretty
import Syntax.CommonTerm
import Syntax.STerms
import Syntax.ATerms
import Syntax.Types
import Syntax.Program

type EnvReader bs a m = (MonadError Error m, MonadReader (Environment bs, a) m)

---------------------------------------------------------------------------------
-- Lookup Terms
---------------------------------------------------------------------------------

lookupDef :: EnvReader bs a m
          => FreeVarName -> m (ATerm () bs, TypeScheme Pos)
lookupDef fv = do
  env <- asks fst
  case M.lookup fv (defEnv env) of
    Nothing -> throwEvalError ["Unbound free variable " <> ppPrint fv <> " not contained in environment."]
    Just res -> return res

lookupPrd :: EnvReader bs a m
          => FreeVarName -> m (STerm Prd () bs, TypeScheme Pos)
lookupPrd fv = do
  env <- asks fst
  case M.lookup fv (prdEnv env) of
    Nothing -> throwEvalError ["Unbound free variable " <> ppPrint fv <> " not contained in environment."]
    Just res -> return res

lookupCns :: EnvReader bs a m
          => FreeVarName -> m (STerm Cns () bs, TypeScheme Neg)
lookupCns fv = do
  env <- asks fst
  case M.lookup fv (cnsEnv env) of
    Nothing -> throwEvalError ["Unbound free variable " <> ppPrint fv <> " not contained in environment."]
    Just res -> return res

---------------------------------------------------------------------------------
-- Lookup Types
---------------------------------------------------------------------------------

envToXtorMap :: Environment bs -> Map XtorName (TypArgs Pos)
envToXtorMap Environment { declEnv } = M.unions xtorMaps
  where
    xtorMaps = xtorSigsToAssocList <$> declEnv
    xtorSigsToAssocList NominalDecl { data_xtors } =
      M.fromList ((\MkXtorSig { sig_name, sig_args } ->(sig_name, sig_args)) <$> data_xtors PosRep)

lookupXtor :: XtorName -> Environment bs -> Maybe DataDecl
lookupXtor xt Environment { declEnv } = find typeContainsXtor declEnv
  where
    typeContainsXtor :: DataDecl -> Bool
    typeContainsXtor NominalDecl { data_xtors } | or (containsXtor <$> data_xtors PosRep) = True
                                   | otherwise = False

    containsXtor :: XtorSig Pos -> Bool
    containsXtor sig = sig_name sig == xt

lookupCase :: EnvReader bs a m
           => XtorName -> m (TypArgs Pos, XtorArgs () FreeVarName)
lookupCase xt = do
  env <- asks fst
  case M.lookup xt (envToXtorMap env) of
    Nothing -> throwGenError ["GenerateConstraints: The xtor " <> ppPrint xt <> " could not be looked up."]
    Just types@(MkTypArgs prdTypes cnsTypes) -> do
      let prds = (\_ -> FreeVar () PrdRep "y") <$> prdTypes
      let cnss = (\_ -> FreeVar () CnsRep "y") <$> cnsTypes
      return (types, MkXtorArgs prds cnss)

lookupDataDecl :: EnvReader bs a m
               => XtorName -> m DataDecl
lookupDataDecl xt = do
  env <- asks fst
  case lookupXtor xt env of
    Nothing -> throwGenError ["Constructor/Destructor " <> ppPrint xt <> " is not contained in program."]
    Just decl -> return decl

lookupXtorSig :: EnvReader bs a m
              => DataDecl -> XtorName -> PolarityRep pol -> m (XtorSig pol)
lookupXtorSig decl xtn pol = do
  case find ( \MkXtorSig{..} -> sig_name == xtn ) (data_xtors decl pol) of
    Just xts -> return xts
    Nothing -> throwGenError ["XtorName " <> unXtorName xtn <> " not found in declaration of type " <> unTypeName (data_name decl)]

---------------------------------------------------------------------------------
-- ChangeEnvironment
---------------------------------------------------------------------------------

withPrd :: EnvReader bs a m
        => FreeVarName -> STerm Prd () bs -> TypeScheme Pos
        -> (m b-> m b)
withPrd fv tm tys m = do
  let modifyEnv (env@Environment { prdEnv }, rest) =
        (env { prdEnv = M.insert fv (tm,tys) prdEnv }, rest)
  local modifyEnv m

withCns :: EnvReader bs a m
        => FreeVarName -> STerm Cns () bs -> TypeScheme Neg
        -> (m b -> m b)
withCns fv tm tys m = do
  let modifyEnv (env@Environment { cnsEnv }, rest) =
        (env { cnsEnv = M.insert fv (tm,tys) cnsEnv }, rest)
  local modifyEnv m

withDef :: EnvReader bs a m
        => FreeVarName -> ATerm () bs -> TypeScheme Pos
        -> (m b -> m b)
withDef fv tm tys m = do
  let modifyEnv (env@Environment { defEnv }, rest) =
        (env { defEnv = M.insert fv (tm,tys) defEnv }, rest)
  local modifyEnv m
