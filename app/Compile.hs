module Compile (runCompile) where

import Control.Monad.Except (runExcept)
import Control.Monad.IO.Class (liftIO)
import Data.Map qualified as M
import Data.Text.IO qualified as T
import System.IO.Error (tryIOError)

import Eval.Eval (eval)
import Parser.Parser (runFileParser)
import Parser.Program (programP)
import Pretty.Pretty (ppPrintIO)
import Translate.Desugar (desugarCmd, desugarEnvironment)
import Translate.Focusing (focusCmd, focusEnvironment)
import Driver.Driver (inferProgramIO, DriverState(..), InferenceOptions(..), defaultInferenceOptions)
import Syntax.Environment (Environment(..))
import Syntax.Kinds (EvaluationOrder(..))
import Syntax.Common

driverState :: DriverState
driverState = DriverState { driverOpts = defaultInferenceOptions { infOptsLibPath = ["examples"]}
                          , driverEnv = mempty }

runCompile :: FilePath -> IO ()
runCompile fp = do
  -- Read in file
  res <- tryIOError (T.readFile fp)
  case res of
    (Left _) -> putStrLn $ "File with name " ++ fp ++ " does not exist."
    (Right file) -> do
        -- Parse file
        let parsedFile = runExcept (runFileParser fp programP file)
        case parsedFile of
            (Left err) -> ppPrintIO err
            (Right prog) -> do
                -- Infer program
                inferredProg <- inferProgramIO driverState prog
                case inferredProg of
                  (Left err) -> ppPrintIO err
                  (Right (env,_inferredProg)) -> do
                    -- Run program
                    case M.lookup (MkFreeVarName "main") (cmdEnv env) of
                      Nothing -> putStrLn "Program does not contain a \"main\" function."
                      Just (cmd,_) -> do
                        let compiledCmd = focusCmd CBV (desugarCmd cmd)
                        let compiledEnv :: Environment Compiled = focusEnvironment CBV (desugarEnvironment env)
                        evalCmd <- liftIO $ eval compiledCmd compiledEnv
                        case evalCmd of
                          Left err -> ppPrintIO err
                          Right res -> ppPrintIO res

