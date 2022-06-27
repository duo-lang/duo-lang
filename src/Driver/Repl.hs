module Driver.Repl
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

import Driver.Definition
    ( DriverM,
      DriverState(drvEnv),
      getSymbolTables,
      liftEitherErr )
import Driver.Driver ( inferDecl, runCompilationModule )
import Eval.Eval ( eval, evalSteps )
import Parser.Definition ( runInteractiveParser )
import Parser.Parser ( subtypingProblemP )
import Parser.Program ( declarationP )
import Parser.Terms ( termP )
import Pretty.Pretty ( ppPrintString )
import Resolution.Definition ( runResolverM )
import Resolution.Types ( resolveTypeScheme )
import Sugar.Desugar ( desugarCmd, desugarEnvironment,  desugarDecl )
import Translate.Focusing ( focusCmd, focusEnvironment )
import Syntax.Common
import Syntax.TST.Program qualified as TST
import Syntax.Core.Program qualified as Core
import TypeAutomata.Subsume ( subsume )
import Utils ( defaultLoc )
import Resolution.Program (resolveDecl)
import Resolution.Terms (resolveCommand)


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
    resolvedDecl <- liftEitherErr (runResolverM sts (resolveDecl decl))
    _ <- inferDecl interactiveModule (desugarDecl resolvedDecl)
    pure ()

---------------------------------------------------------------------------------
-- Running a command in the repl
---------------------------------------------------------------------------------

data EvalSteps = Steps | NoSteps

runCmd :: Text -> EvalSteps ->  DriverM ()
runCmd txt steps = do
    (parsedCommand, _) <- runInteractiveParser termP txt
    sts <- getSymbolTables
    resolvedDecl <- liftEitherErr (runResolverM sts (resolveCommand parsedCommand))
    let cmdDecl = Core.MkCommandDeclaration defaultLoc Nothing (MkFreeVarName "main") (desugarCmd resolvedDecl)
    (TST.CmdDecl TST.MkCommandDeclaration { cmddecl_cmd }) <- inferDecl interactiveModule (Core.CmdDecl cmdDecl)
    env <- gets drvEnv
    let compiledCmd = focusCmd CBV cmddecl_cmd
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
    resolved_t1 <- liftEitherErr (runResolverM sts (resolveTypeScheme PosRep t1))
    resolved_t2 <- liftEitherErr (runResolverM sts (resolveTypeScheme PosRep t2))
    isSubsumed <- liftEitherErr $ (subsume PosRep resolved_t1 resolved_t2,[])
    liftIO $ putStrLn $ if isSubsumed
                        then "Subsumption holds"
                        else "Subsumption doesn't hold"
