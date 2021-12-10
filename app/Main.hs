module Main where

import Data.Version (showVersion)
import Options.Applicative

import Options
import Compile (runCompile)
import Repl.Run (runRepl)
import LSP.LSP (runLSP)
import Paths_dualsub (version)

main :: IO ()
main = do
    opts <- execParser optParserInfo
    dispatch opts

dispatch :: Options -> IO ()
dispatch OptRepl         = runRepl
dispatch OptLSP          = runLSP
dispatch (OptCompile fp) = runCompile fp
dispatch OptVersion      = putStrLn (showVersion version)
