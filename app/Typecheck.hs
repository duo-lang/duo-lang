
module Typecheck where

import Options (DebugFlags(..))
import Syntax.RST.Names
import Driver.Driver (runCompilationModule, defaultInferenceOptions)
import Driver.Definition (defaultDriverState, execDriverM, DriverState(..), setPrintGraphOpts, setDebugOpts)
import Pretty.Errors (printLocatedReport)
import qualified Data.Text as T
import System.Exit (exitWith, ExitCode (ExitFailure))

runTypecheck :: DebugFlags -> ModuleName -> IO ()
runTypecheck DebugFlags { df_debug, df_printGraphs } mn = do
  (res,warnings) <- execDriverM driverState $ runCompilationModule mn
  mapM_ printLocatedReport warnings
  case res of
    Left errs -> do
      mapM_ printLocatedReport errs
      exitWith (ExitFailure 1)
    Right (_, MkDriverState {}) -> do
      putStrLn $ "Module " <> T.unpack (unModuleName mn) <> " typechecks"
  return ()
    where
      driverState = defaultDriverState { drvOpts = infOpts }
      infOpts = (if df_printGraphs then setPrintGraphOpts else id) infOpts'
      infOpts' = (if df_debug then setDebugOpts else id) defaultInferenceOptions
