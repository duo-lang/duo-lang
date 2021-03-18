module TypeInference.InferProgram ( insertDecl, inferProgram )where

import Data.Bifunctor (first)
import qualified Data.Map as M

import TypeInference.InferTypes
import Syntax.CommonTerm
import Syntax.Program
import Utils

insertDecl :: Declaration () -> Environment -> Either LocatedError Environment
insertDecl (PrdDecl loc v t)  env@Environment { prdEnv }  = do
  ty <- first (Located loc) $ inferSTerm PrdRep t env
  return $ env { prdEnv  = M.insert v (t,ty) prdEnv }
insertDecl (CnsDecl loc v t)  env@Environment { cnsEnv }  = do
  ty <- first (Located loc) $ inferSTerm CnsRep t env
  return $ env { cnsEnv  = M.insert v (t,ty) cnsEnv }
insertDecl (CmdDecl loc v t)  env@Environment { cmdEnv }  = do
  first (Located loc) $ checkCmd t env
  return $ env { cmdEnv  = M.insert v t cmdEnv }
insertDecl (DefDecl loc v t)  env@Environment { defEnv }  = do
  ty <- first (Located loc) $ inferATerm t env
  return $ env { defEnv  = M.insert v (t,ty) defEnv }
insertDecl (DataDecl _loc dcl) env@Environment { declEnv } = do
  return $ env { declEnv = dcl : declEnv }

inferProgram :: [Declaration ()] -> Either LocatedError Environment
inferProgram = inferProgram' mempty
  where
    inferProgram' :: Environment -> [Declaration ()] -> Either LocatedError Environment
    inferProgram' env [] = return env
    inferProgram' env (decl:decls) = do
      env' <- insertDecl decl env
      inferProgram' env' decls
