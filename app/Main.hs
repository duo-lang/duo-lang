module Main where

import System.Environment (getArgs)
import Repl.Run (runRepl)
import LSP.LSP (runLSP)

main :: IO ()
main = do
    args <- getArgs
    dispatch args

dispatch :: [String] -> IO ()
dispatch ["lsp"] = runLSP
dispatch _       = runRepl

