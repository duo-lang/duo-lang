{-# LANGUAGE TemplateHaskell #-}
module Main where

import Data.Version (showVersion)
import GitHash (tGitInfoCwdTry, giHash, giBranch)

import Options (Options(..), parseOptions)
import Run (runRun)
import Syntax.CST.Names
import Typecheck (runTypecheck)
import Deps (runDeps)
import LSP.LSP (runLSP)
import Paths_duo_lang (version)
import Utils (trimStr, filePathToModuleName)
import GHC.IO.Encoding (setLocaleEncoding)
import System.IO (utf8)
import System.Directory (doesFileExist)
import Parser.Program (moduleNameP)
import qualified Data.Text as T
import Parser.Definition (runInteractiveParser)

main :: IO ()
main = do
    setLocaleEncoding utf8
    opts <- parseOptions
    dispatch opts

-- subcommands requiring a module as argument can accept file paths and module names
-- this is some preprocessing before passing it to the respective functions
getModuleName :: String -> IO (Either FilePath ModuleName)
getModuleName fp = do
    let fp' = trimStr fp
    exists <- doesFileExist fp'
    if exists
        then pure $ Left fp'
        else 
            let mmn = runInteractiveParser moduleNameP $ T.pack fp'
            in case mmn of
                 Left _e -> pure $ pure $ filePathToModuleName fp'
                 Right mn -> pure (pure $ fst mn)

dispatch :: Options -> IO ()
dispatch OptLSP                 = runLSP
dispatch (OptRun fp opts)       = runRun opts =<< getModuleName fp
dispatch (OptDeps fp)           = runDeps =<< getModuleName fp
dispatch OptVersion             = printVersion
dispatch (OptTypecheck fp opts) = runTypecheck opts =<< getModuleName fp

printVersion :: IO ()
printVersion = do
    putStrLn $ "Duo Version: " <> showVersion version
    let gitry = $$tGitInfoCwdTry
    case gitry of
        Left _ -> pure ()
        Right gi -> do
          putStrLn $ "Git Commit: " <> giHash gi
          putStrLn $ "Git Branch: " <> giBranch gi
