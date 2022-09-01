{-# LANGUAGE TemplateHaskell #-}
module Main where

import Data.Text qualified as T
import Data.Version (showVersion)
import GitHash (tGitInfoCwd, giHash, giBranch)
import System.FilePath (takeBaseName, replaceFileName)

import Options (Options(..), parseOptions)
import Run (runRun)
import Syntax.CST.Names
import Typecheck (runTypecheck)
import Deps (runDeps)
import Repl.Run (runRepl)
import LSP.LSP (runLSP)
import Paths_duo_lang (version)
import Utils (trimStr)

main :: IO ()
main = do
    opts <- parseOptions
    dispatch opts

filepathToModuleName :: FilePath -> ModuleName
filepathToModuleName fp = MkModuleName . T.pack . trimStr . replaceFileName fp $ takeBaseName fp

dispatch :: Options -> IO ()
dispatch OptRepl                = runRepl
dispatch (OptLSP log)           = runLSP log
dispatch (OptRun fp opts)       = runRun opts $ filepathToModuleName fp
dispatch (OptDeps fp)           = runDeps $ filepathToModuleName fp
dispatch OptVersion             = printVersion
dispatch (OptTypecheck fp opts) = runTypecheck opts $ filepathToModuleName fp

printVersion :: IO ()
printVersion = do
    let gi = $$tGitInfoCwd
    putStrLn $ "Duo Version: " <> showVersion version
    putStrLn $ "Git Commit: " <> giHash gi
    putStrLn $ "Git Branch: " <> giBranch gi
