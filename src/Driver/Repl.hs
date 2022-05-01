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

import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.Text (Text)
import Data.Text qualified as T

import Driver.Definition
import Driver.Driver
import Parser.Definition
import Parser.Parser ( subtypingProblemP )
import Parser.Program ( declarationP )
import Renamer.Definition
import Renamer.Types
import Syntax.Common
import TypeAutomata.Subsume
import Utils ( defaultLoc )
import Renamer.Program (renameDecl)


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
loadFromModule mn = do
    fp <- findModule mn defaultLoc
    loadFromFile fp


-- loadFile :: FilePath -> Repl ()
-- loadFile fp = do
--   decls <- parseFile fp programP
--   ds <- gets replDriverState
--   res <- liftIO $ inferProgramIO ds (MkModuleName "<Interactive>") decls
--   case res of
--     Left err -> printLocatedError err
--     Right (_newEnv,_) -> do
--       --modifyEnvironment (MkModuleName "FOO") undefined --(const newEnv)
--       --prettyRepl newEnv
--       prettyRepl $ "Successfully loaded: " ++ fp

reload :: DriverM ()
reload = liftIO $ putStrLn ":reload currently not implemented"

---------------------------------------------------------------------------------
-- ":let" command
---------------------------------------------------------------------------------

letRepl :: Text -> DriverM ()
letRepl txt = do
    decl <- runInteractiveParser declarationP txt
    sts <- getSymbolTables
    renamedDecl <- liftEitherErr (runRenamerM sts (renameDecl decl))
    _ <- inferDecl interactiveModule renamedDecl
    pure ()

---------------------------------------------------------------------------------
-- Running a command in the repl
---------------------------------------------------------------------------------

data EvalSteps = Steps | NoSteps

runCmd :: Text -> EvalSteps ->  DriverM ()
runCmd _s _steps = liftIO $ putStrLn "run currently not implemented"
-- do
--   (comLoc,_) <- parseInteractive termP (T.pack s)
--   ds <- gets replDriverState
--   inferredCmd <- liftIO $ inferProgramIO ds (MkModuleName "<Interactive>") [CST.CmdDecl defaultLoc Nothing (MkFreeVarName "main") comLoc]
--   case inferredCmd of
--     Right (_,[CmdDecl _ _ _ inferredCmd]) -> do
--       env <- gets (drvEnv . replDriverState)
--       steps <- gets steps
--       let compiledCmd = focusCmd CBV (desugarCmd inferredCmd)
--       let compiledEnv = focusEnvironment CBV (desugarEnvironment env)
--       case steps of
--         NoSteps -> do
--           resE <- liftIO $ eval compiledCmd compiledEnv
--           res <- fromRight resE
--           prettyRepl res
--         Steps -> do
--           resE <- liftIO $ evalSteps compiledCmd compiledEnv
--           res <- fromRight  resE
--           forM_ res (\cmd -> prettyRepl cmd >> prettyText "----")
--     Right _ -> prettyText "Unreachable"
--     Left err -> prettyRepl err

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

-- safeRead :: FilePath -> Repl Text
-- safeRead file =  do
--   let file' = trimStr file
--   res <- liftIO $ tryIOError (T.readFile file')
--   case res of
--     (Left _) -> do
--       liftIO $ putStrLn $ "File with name " ++ file' ++ " does not exist."
--       abort
--     (Right s) -> return $ s