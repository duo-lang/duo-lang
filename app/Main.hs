{-# LANGUAGE TemplateHaskell #-}
module Main where

import Data.Version (showVersion)
import Development.GitRev (gitHash, gitBranch)

import Options (Options(..), parseOptions)
import Compile (runCompile)
import Repl.Run (runRepl)
import LSP.LSP (runLSP)
import Paths_dualsub (version)

main :: IO ()
main = do
    opts <- parseOptions
    dispatch opts

dispatch :: Options -> IO ()
dispatch OptRepl         = runRepl
dispatch (OptLSP log)    = runLSP log
dispatch (OptCompile fp) = runCompile fp
dispatch OptVersion      = printVersion

printVersion :: IO ()
printVersion = do
    putStrLn $ "DualSub Version: " <> showVersion version
    putStrLn $ "Git Commit: " <> $(gitHash)
    putStrLn $ "Git Branch: " <> $(gitBranch)