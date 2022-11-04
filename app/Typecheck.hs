
module Typecheck where

import Options (DebugFlags(..))
import Syntax.CST.Names
import Driver.Driver (runCompilationModule, defaultInferenceOptions)
import Driver.Definition (defaultDriverState, execDriverM, DriverState(..), setPrintGraphOpts, setDebugOpts, addModule)
import Pretty.Errors (printLocatedReport)
import qualified Data.Text as T
import System.Exit (exitWith, ExitCode (ExitFailure))
import Data.List (intersperse)
import Data.Foldable (fold)
import qualified Data.Text.IO as T
import Control.Monad.IO.Class (liftIO)
import Parser.Definition (runFileParser)
import Syntax.CST.Program (adjustModulePath, Module (..))
import Parser.Program (moduleP)
import Control.Monad.Except (throwError)

runTypecheck :: DebugFlags -> Either FilePath ModuleName -> IO ()
runTypecheck DebugFlags { df_debug, df_printGraphs } modId = do
  (res ,warnings) <- case modId of
            Left fp -> do
              file <- liftIO $ T.readFile fp
              execDriverM driverState $ do
                mod <- runFileParser fp (moduleP fp) file
                case adjustModulePath mod fp of
                  Right mod -> do
                      let mn = mod_name mod
                      addModule mod
                      res <- runCompilationModule mn
                      pure (mn,res)
                  Left e -> throwError e
            Right mn -> execDriverM driverState $ runCompilationModule mn >>= \res -> pure (mn, res)
  mapM_ printLocatedReport warnings
  case res of
    Left errs -> do
      mapM_ printLocatedReport errs
      exitWith (ExitFailure 1)
    Right ((mn,_), MkDriverState {}) -> do
      putStrLn $ "Module " <> T.unpack (fold (intersperse "." (mn_path mn ++  [mn_base mn]))) <> " typechecks"
  return ()
    where
      driverState = defaultDriverState { drvOpts = infOpts }
      infOpts = (if df_printGraphs then setPrintGraphOpts else id) infOpts'
      infOpts' = (if df_debug then setDebugOpts else id) defaultInferenceOptions
