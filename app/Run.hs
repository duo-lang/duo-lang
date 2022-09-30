module Run (runRun) where

import Control.Monad.IO.Class (liftIO)
import Data.Foldable (fold)
import Data.Map qualified as M

import Driver.Definition
import Driver.Driver ( runCompilationModule )
import Driver.Repl (desugarEnv)
import Eval.Definition (EvalEnv)
import Eval.Eval (eval)
import Syntax.CST.Names
import Syntax.CST.Kinds
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Translate.Focusing (Focus(..) )
import Loc ( defaultLoc )
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
      let compiledEnv :: EvalEnv = focus CBV ((\map -> fold $ desugarEnv <$> M.elems map) drvEnv)
      evalCmd <- liftIO $ eval (TST.Jump defaultLoc (MkFreeVarName "main")) compiledEnv
      case evalCmd of
          Left errs -> mapM_ printLocatedReport errs
          Right _res -> return ()
    where
      driverState = defaultDriverState { drvOpts = infOpts }
      infOpts = (if df_printGraphs then setPrintGraphOpts else id) infOpts'
      infOpts' = (if df_debug then setDebugOpts else id) defaultInferenceOptions

