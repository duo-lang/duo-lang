module Compile (runCompile) where

import Control.Monad.IO.Class (liftIO)

import Driver.Definition
import Driver.Driver ( runCompilationModule )
import Eval.Definition (EvalEnv)
import Eval.Eval (eval)
import Pretty.Pretty (ppPrintIO)
import Syntax.Common
import Syntax.AST.Program qualified as AST
import Syntax.AST.Terms qualified as AST
import Sugar.Desugar (desugarEnvironment)
import Translate.Focusing (focusEnvironment)
import Utils ( defaultLoc )

driverAction :: ModuleName -> DriverM AST.Program
driverAction mn = do
  runCompilationModule mn
  queryTypecheckedProgram mn


runCompile :: ModuleName -> IO ()
runCompile mn = do
  res <- liftIO $ execDriverM defaultDriverState (driverAction mn)
  case res of
    Left err -> ppPrintIO err
    Right (_, MkDriverState { drvEnv }) -> do
      -- Run program
      let compiledEnv :: EvalEnv = focusEnvironment CBV (desugarEnvironment drvEnv)
      evalCmd <- liftIO $ eval (AST.Jump defaultLoc (MkFreeVarName "main")) compiledEnv
      case evalCmd of
          Left err -> ppPrintIO err
          Right res -> ppPrintIO res

