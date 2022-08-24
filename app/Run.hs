module Run (runRun) where

import Control.Monad.IO.Class (liftIO)

import Driver.Definition
import Driver.Driver ( runCompilationModule )
import Eval.Definition (EvalEnv)
import Eval.Eval (eval)
import Pretty.Pretty (ppPrintIO)
import Syntax.CST.Names
import Syntax.CST.Kinds
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Sugar.Desugar (desugarEnvironment)
import Translate.Focusing (focusEnvironment)
import Utils ( defaultLoc )
import Options (DebugFlags(..))
import Pretty.Errors (printLocatedReport)

driverAction :: ModuleName -> DriverM TST.Module
driverAction mn = do
  runCompilationModule mn
  queryTypecheckedModule mn


runRun :: DebugFlags -> ModuleName -> IO ()
runRun DebugFlags { df_debug, df_printGraphs } mn = do
  (res, warnings) <- execDriverM driverState (driverAction mn)
  mapM_ printLocatedReport warnings
  case res of
    Left errs -> mapM_ printLocatedReport errs
    Right (_, MkDriverState { drvEnv }) -> do
      -- Run program
      let compiledEnv :: EvalEnv = focusEnvironment CBV (desugarEnvironment drvEnv)
      evalCmd <- liftIO $ eval (TST.Jump defaultLoc (MkFreeVarName "main")) compiledEnv
      case evalCmd of
          Left errs -> mapM_ printLocatedReport errs
          Right res -> ppPrintIO res
    where
      driverState = defaultDriverState { drvOpts = infOpts }
      infOpts = (if df_printGraphs then setPrintGraphOpts else id) infOpts'
      infOpts' = (if df_debug then setDebugOpts else id) defaultInferenceOptions

