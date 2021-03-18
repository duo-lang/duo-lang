module TypeInference.InferProgram ( insertDecl, inferProgram )where

import qualified Data.Map as M

import Syntax.Program
import Utils

insertDecl :: Declaration () -> Environment -> Environment
insertDecl (PrdDecl v t)  env@Environment { prdEnv }  = env { prdEnv  = M.insert v (t,undefined) prdEnv }
insertDecl (CnsDecl v t)  env@Environment { cnsEnv }  = env { cnsEnv  = M.insert v (t,undefined) cnsEnv }
insertDecl (CmdDecl v t)  env@Environment { cmdEnv }  = env { cmdEnv  = M.insert v t cmdEnv }
insertDecl (DefDecl v t)  env@Environment { defEnv }  = env { defEnv  = M.insert v (t,undefined) defEnv }
insertDecl (DataDecl dcl) env@Environment { declEnv } = env { declEnv = dcl : declEnv }

inferProgram :: [Declaration ()] -> Either Error Environment
inferProgram decls = return $ foldr insertDecl mempty decls
