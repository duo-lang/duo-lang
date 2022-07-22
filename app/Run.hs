module Run (runRun) where

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
import Options (DebugFlags(..))

driverAction :: ModuleName -> DriverM TST.Program
driverAction mn = do
  runCompilationModule mn
  queryTypecheckedProgram mn


runRun :: DebugFlags -> ModuleName -> IO ()
runRun DebugFlags { df_debug, df_printGraphs } mn = do
  (res, warnings) <- execDriverM driverState (driverAction mn)
  mapM_ ppPrintIO warnings
  case res of
    Left errs -> mapM_ ppPrintIO errs
    Right (_, MkDriverState { drvEnv }) -> do
      -- Run program
      let compiledEnv :: EvalEnv = focusEnvironment CBV (desugarEnvironment drvEnv)
      evalCmd <- liftIO $ eval (TST.Jump defaultLoc (MkFreeVarName "main")) compiledEnv
      case evalCmd of
          Left errs -> mapM_ ppPrintIO errs
          Right res -> ppPrintIO res
    where
      driverState = defaultDriverState { drvOpts = infOpts }
      infOpts = (if df_printGraphs then setPrintGraphOpts else id) infOpts'
      infOpts' = (if df_debug then setDebugOpts else id) defaultInferenceOptions

