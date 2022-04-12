module Compile (runCompile) where

import Control.Monad.IO.Class (liftIO)
import Data.Map qualified as M

import Driver.Definition
import Driver.Driver
import Driver.Environment (Environment(..))
import Eval.Definition (EvalEnv)
import Eval.Eval (eval)
import Pretty.Pretty (ppPrintIO)
import Syntax.Common
import Syntax.AST.Program qualified as AST
import Translate.Desugar (desugarCmd, desugarEnvironment)
import Translate.Focusing (focusCmd, focusEnvironment)

driverAction :: ModuleName -> DriverM (AST.Program)
driverAction mn = do
  runCompilationModule mn
  queryTypecheckedProgram mn


runCompile :: ModuleName -> IO ()
runCompile mn = do
  res <- liftIO $ execDriverM defaultDriverState (driverAction mn)
  case res of
    Left err -> ppPrintIO err
    Right (_, MkDriverState { driverEnv }) -> do
      -- Run program
      case M.lookup (MkFreeVarName "main") (cmdEnv driverEnv) of
        Nothing -> putStrLn "Program does not contain a \"main\" function."
        Just (cmd,_) -> do
          let compiledCmd = focusCmd CBV (desugarCmd cmd)
          let compiledEnv :: EvalEnv = focusEnvironment CBV (desugarEnvironment driverEnv)
          evalCmd <- liftIO $ eval compiledCmd compiledEnv
          case evalCmd of
            Left err -> ppPrintIO err
            Right res -> ppPrintIO res

