module TypeInference.InferProgram where

import qualified Data.Map as M
import Syntax.Program

insertDecl :: Declaration () -> Environment -> Environment
insertDecl (PrdDecl v t)  env@Environment { prdEnv }  = env { prdEnv  = M.insert v t prdEnv }
insertDecl (CnsDecl v t)  env@Environment { cnsEnv }  = env { cnsEnv  = M.insert v t cnsEnv }
insertDecl (CmdDecl v t)  env@Environment { cmdEnv }  = env { cmdEnv  = M.insert v t cmdEnv }
insertDecl (DefDecl v t)  env@Environment { defEnv }  = env { defEnv  = M.insert v t defEnv }
insertDecl (DataDecl dcl) env@Environment { declEnv } = env { declEnv = dcl : declEnv }

createEnv :: [Declaration ()] -> Environment
createEnv = foldr insertDecl mempty 
