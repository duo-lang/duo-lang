module Compile (runCompile) where

import Control.Monad.IO.Class (liftIO)

import Driver.Definition
import Driver.Driver ( runCompilationModule )
import Eval.Definition (EvalEnv)
import Eval.Eval (eval)
import Pretty.Pretty (ppPrintIO)
import Syntax.Common
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Sugar.Desugar (desugarEnvironment)
import Translate.Focusing (focusEnvironment)
import Utils ( defaultLoc )

driverAction :: ModuleName -> DriverM TST.Program
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
      evalCmd <- liftIO $ eval (TST.Jump defaultLoc (MkFreeUniVarName "main")) compiledEnv
      case evalCmd of
          Left err -> ppPrintIO err
          Right res -> ppPrintIO res

