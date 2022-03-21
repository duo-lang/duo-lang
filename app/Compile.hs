module Compile (runCompile) where

import Data.Map qualified as M

import Eval.Eval (eval)
import Pretty.Pretty (ppPrintIO)
import Translate.Desugar (desugarCmd, desugarEnvironment)
import Translate.Focusing (focusCmd, focusEnvironment)
import Driver.Driver (inferProgram, DriverState(..), InferenceOptions(..), defaultInferenceOptions, execDriverM)
import Syntax.Environment (Environment(..))
import Syntax.Kinds (EvaluationOrder(..))
import Syntax.Common

driverState :: DriverState
driverState = DriverState { driverOpts = defaultInferenceOptions { infOptsLibPath = ["examples"]}
                          , driverEnv = mempty }

runCompile :: FilePath -> IO ()
runCompile fp = do
  res <- execDriverM driverState mempty (inferProgram fp)
  case res of
    Left err -> ppPrintIO err
    Right ((_,_,env),_) -> do
      case M.lookup (MkFreeVarName "main") (cmdEnv env) of
          Nothing -> putStrLn "Program does not contain a \"main\" function."
          Just (cmd,_) -> do
                let compiledCmd = focusCmd CBV (desugarCmd cmd)
                let compiledEnv :: Environment Compiled = focusEnvironment CBV (desugarEnvironment env)
                evalCmd <- eval compiledCmd compiledEnv
                case evalCmd of
                    Left err -> ppPrintIO err
                    Right res -> ppPrintIO res

