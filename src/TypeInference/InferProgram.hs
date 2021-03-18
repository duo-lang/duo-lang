module TypeInference.InferProgram ( insertDecl, inferProgram )where

import qualified Data.Map as M

import Syntax.Program
import Utils

insertDecl :: Declaration () -> Environment -> Either Error Environment
insertDecl (PrdDecl v t)  env@Environment { prdEnv }  = return $ env { prdEnv  = M.insert v (t,undefined) prdEnv }
insertDecl (CnsDecl v t)  env@Environment { cnsEnv }  = return $ env { cnsEnv  = M.insert v (t,undefined) cnsEnv }
insertDecl (CmdDecl v t)  env@Environment { cmdEnv }  = return $ env { cmdEnv  = M.insert v t cmdEnv }
insertDecl (DefDecl v t)  env@Environment { defEnv }  = return $ env { defEnv  = M.insert v (t,undefined) defEnv }
insertDecl (DataDecl dcl) env@Environment { declEnv } = return $ env { declEnv = dcl : declEnv }

inferProgram :: [Declaration ()] -> Either Error Environment
inferProgram = inferProgram' mempty
  where
    inferProgram' :: Environment -> [Declaration ()] -> Either Error Environment
    inferProgram' env [] = return env
    inferProgram' env (decl:decls) = do
      env' <- insertDecl decl env
      inferProgram' env' decls
