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
  , subsume
  ) where

import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.Text (Text)

import Driver.Definition ( DriverM )

---------------------------------------------------------------------------------
-- ":load" and ":reload" commands
---------------------------------------------------------------------------------

load :: Text -> DriverM ()
load = undefined

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
letRepl s = undefined --do
--   decl <- fromRight (runExcept (runInteractiveParser declarationP s))
--   ds <- gets replDriverState
--   newEnv <- liftIO (inferProgramIO ds (MkModuleName "<Interactive>") [decl])
--   case newEnv of
--     Left err -> prettyText (T.pack $ show err)
--     Right (env,_) -> undefined -- modifyEnvironment undefined undefined --(const env)undefined


---------------------------------------------------------------------------------
-- Running a command in the repl
---------------------------------------------------------------------------------

data EvalSteps = Steps | NoSteps

runCmd :: Text -> EvalSteps ->  DriverM ()
runCmd s = undefined
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

subsume :: Text -> DriverM ()
subsume = undefined
--  (t1,t2) <- parseInteractive subtypingProblemP s
--  let t1' = runRenamerM M.empty $ renameTypeScheme PosRep t1
--  let t2' = runRenamerM M.empty $ renameTypeScheme PosRep t2
--  case (t1', t2') of
{-      (Right res1, Right res2) -> do
       res <- fromRight (subsume PosRep res1 res2)
       prettyRepl res
     (_,_) -> fail "SubtypingProblemP: Cannot lower types." -}

-- safeRead :: FilePath -> Repl Text
-- safeRead file =  do
--   let file' = trimStr file
--   res <- liftIO $ tryIOError (T.readFile file')
--   case res of
--     (Left _) -> do
--       liftIO $ putStrLn $ "File with name " ++ file' ++ " does not exist."
--       abort
--     (Right s) -> return $ s