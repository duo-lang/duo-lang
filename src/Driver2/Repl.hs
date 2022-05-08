module Driver2.Repl
  ( -- :load and :reloadloadwhere
    load
  , reload
    -- ":let"
  , letRepl
    -- Running a command
  , EvalSteps(..)
  , runCmd
    -- ":subsume"
  , subsumeRepl
  ) where

import Control.Monad.State (gets)
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.Text (Text)
import Data.Text qualified as T

import Driver2.Definition
    ( DriverM,
      DriverState(drvEnv),
      getSymbolTables,
      liftEitherErr )
import Driver2.Driver ( inferDecl, runCompilationModule )
import Eval2.Eval ( eval, evalSteps )
import Parser.Definition ( runInteractiveParser )
import Parser.Parser ( subtypingProblemP )
import Parser.Program ( declarationP )
import Parser.Terms ( termP )
import Pretty.Pretty ( ppPrintString )
import Renamer.Definition ( runRenamerM )
import Renamer.Types ( renameTypeScheme )
import Sugar.Desugar2 ( desugarCmd, desugarEnvironment, desugarProgram, desugarDecl )
import Translate.Focusing2 ( focusCmd, focusEnvironment )
import Syntax.Common
import Syntax.RST.Program qualified as RST
import Syntax.AST.Program qualified as AST
import Syntax.Core.Program qualified as Core
import TypeAutomata.Subsume ( subsume )
import Utils ( defaultLoc )
import Renamer.Program (renameDecl)
import Renamer.Terms (renameCommand)


---------------------------------------------------------------------------------
-- The special "<interactive>" module
---------------------------------------------------------------------------------

interactiveModule :: ModuleName 
interactiveModule = MkModuleName "<Interactive>"

---------------------------------------------------------------------------------
-- ":load" and ":reload" commands
---------------------------------------------------------------------------------

load :: Text -> DriverM ()
load txt = if T.isSuffixOf ".ds" txt
           then loadFromFile (T.unpack txt)
           else loadFromModule (MkModuleName txt)

-- | The user has called ":load" with a filepath.
loadFromFile :: FilePath -> DriverM ()
loadFromFile _fp = liftIO $ putStrLn "load from file"

-- | The user has called ":load" with a module name
loadFromModule :: ModuleName -> DriverM ()
loadFromModule mn = runCompilationModule  mn

reload :: DriverM ()
reload = pure ()

---------------------------------------------------------------------------------
-- ":let" command
---------------------------------------------------------------------------------

letRepl :: Text -> DriverM ()
letRepl txt = do
    decl <- runInteractiveParser declarationP txt
    sts <- getSymbolTables
    renamedDecl <- liftEitherErr (runRenamerM sts (renameDecl decl))
    _ <- inferDecl interactiveModule (desugarDecl renamedDecl)
    pure ()

---------------------------------------------------------------------------------
-- Running a command in the repl
---------------------------------------------------------------------------------

data EvalSteps = Steps | NoSteps

runCmd :: Text -> EvalSteps ->  DriverM ()
runCmd txt steps = do
    (parsedCommand, _) <- runInteractiveParser termP txt
    sts <- getSymbolTables
    renamedDecl <- liftEitherErr (runRenamerM sts (renameCommand parsedCommand))
    (AST.CmdDecl _ _ _ inferredCmd) <- inferDecl interactiveModule (Core.CmdDecl defaultLoc Nothing (MkFreeVarName "main") (desugarCmd renamedDecl))
    env <- gets drvEnv
    let compiledCmd = focusCmd CBV inferredCmd   
    let compiledEnv = focusEnvironment CBV (desugarEnvironment env)
    case steps of
        NoSteps -> do
            resE <- liftIO $ eval compiledCmd compiledEnv
            liftIO $ putStrLn $ case resE of
                                   Left err -> ppPrintString err
                                   Right res -> ppPrintString res
        Steps -> do
            resE <-liftIO $ evalSteps compiledCmd compiledEnv
            liftIO $ putStrLn $ case resE of
                                   Left err -> ppPrintString err
                                   Right res -> ppPrintString res

---------------------------------------------------------------------------------
-- ":subsume" command
---------------------------------------------------------------------------------

subsumeRepl :: Text -> DriverM ()
subsumeRepl txt = do
    (t1,t2) <- runInteractiveParser subtypingProblemP txt
    sts <- getSymbolTables
    renamed_t1 <- liftEitherErr (runRenamerM sts (renameTypeScheme PosRep t1))
    renamed_t2 <- liftEitherErr (runRenamerM sts (renameTypeScheme PosRep t2))
    isSubsumed <- liftEitherErr $ subsume PosRep renamed_t1 renamed_t2
    liftIO $ putStrLn $ if isSubsumed
                        then "Subsumption holds"
                        else "Subsumption doesn't hold"
