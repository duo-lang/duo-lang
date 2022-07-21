
module Typecheck where

import Options (DebugFlags(..))
import Syntax.Common
import Driver.Driver (runCompilationModule, defaultInferenceOptions)
import Driver.Definition (defaultDriverState, execDriverM, DriverState(..), InferenceOptions(..), setPrintGraphOpts, setDebugOpts)
import Utils (Verbosity(..))
import Control.Monad.IO.Class (MonadIO(liftIO))
import Pretty.Pretty (ppPrintIO)
import qualified Data.Text as T

runTypecheck :: DebugFlags -> ModuleName -> IO ()
runTypecheck DebugFlags { tcf_debug, tcf_printGraphs } mn = do
  print tcf_debug
  (res,warnings) <- execDriverM driverState $ runCompilationModule mn
  mapM_ ppPrintIO warnings
  case res of
    Left errs -> mapM_ ppPrintIO errs
    Right (_, MkDriverState {}) -> do
      putStrLn $ "Module " <> T.unpack (unModuleName mn) <> " typechecks"
  return ()
    where
      driverState = defaultDriverState { drvOpts = infOpts }
      infOpts = (if tcf_printGraphs then setPrintGraphOpts else id) infOpts'
      infOpts' = (if tcf_debug then setDebugOpts else id) defaultInferenceOptions
