{-# LANGUAGE TemplateHaskell #-}
module Main where

import Data.Text qualified as T
import Data.Version (showVersion)
import GitHash (tGitInfoCwd, giHash, giBranch)

import Options (Options(..), parseOptions)
import Compile (runCompile)
import Typecheck (runTypecheck)
import Deps (runDeps)
import Repl.Run (runRepl)
import LSP.LSP (runLSP)
import Paths_duo_lang (version)
import Syntax.Common
import Utils (trimStr)

main :: IO ()
main = do
    opts <- parseOptions
    dispatch opts

filepathToModuleName :: FilePath -> ModuleName
filepathToModuleName = MkModuleName . T.pack . trimStr

dispatch :: Options -> IO ()
dispatch OptRepl         = runRepl
dispatch (OptLSP log)    = runLSP log
dispatch (OptCompile fp) = runCompile $ filepathToModuleName fp
dispatch (OptDeps fp)    = runDeps $ filepathToModuleName fp
dispatch OptVersion      = printVersion
dispatch (OptTypecheck fp opts) = runTypecheck (filepathToModuleName fp) opts

printVersion :: IO ()
printVersion = do
    let gi = $$tGitInfoCwd
    putStrLn $ "Duo Version: " <> showVersion version
    putStrLn $ "Git Commit: " <> giHash gi
    putStrLn $ "Git Branch: " <> giBranch gi
