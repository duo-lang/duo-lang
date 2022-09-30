module Options
  ( Options(..)
  , DebugFlags(..)
  , parseOptions
  ) where

import Data.Foldable (fold)
import Options.Applicative

data Options where
    OptLSP :: Maybe FilePath -> Options
    OptRun :: FilePath -> DebugFlags -> Options
    OptTypecheck :: FilePath -> DebugFlags -> Options
    OptDeps :: FilePath -> Options
    OptVersion :: Options

---------------------------------------------------------------------------------
-- Debug flags
---------------------------------------------------------------------------------

data DebugFlags = DebugFlags { df_debug :: Bool, df_printGraphs :: Bool }

debugFlagParser :: Parser DebugFlags
debugFlagParser = DebugFlags <$> switch modsDebug <*> switch modsGraph
  where
    modsDebug = fold  [ long "XDebug"
                      , help "Print debug info."
                      ]
    modsGraph = fold  [ long "XPrintGraph"
                      , help "Print simplification automata graphs."
                      ]

---------------------------------------------------------------------------------
-- Commandline options for starting a LSP session
---------------------------------------------------------------------------------

lspParser :: Parser Options
lspParser = OptLSP <$> optional (strOption mods)
  where
    mods = fold [ long "logfile"
                , short 'l'
                , metavar "FILE"
                , help "Specify the FILE that the LSP server will use for printing logs. If a logfile is not specified, output is directed to stderr."
                ]


lspParserInfo :: ParserInfo Options
lspParserInfo = info (helper <*> lspParser) mods
  where
    mods = fold [ fullDesc
                , header "duo lsp - Start a LSP session"
                , progDesc "Start a LSP session. This command should only be invoked by editors or for debugging purposes."
                ]

---------------------------------------------------------------------------------
-- Commandline options for typechecking source files
---------------------------------------------------------------------------------

typecheckParser :: Parser Options
typecheckParser = OptTypecheck <$> argument str mods <*> debugFlagParser
  where
    mods = fold [ metavar "TARGET"
                , help "Filepath of the source file."
                ]

typecheckParserInfo :: ParserInfo Options
typecheckParserInfo = info (helper <*> typecheckParser) mods
  where
    mods = fold [ fullDesc
                , header "duo check - Typecheck Duo source files"
                , progDesc "Typecheck Duo source files."
                ]

---------------------------------------------------------------------------------
-- Commandline options for running source files
---------------------------------------------------------------------------------

runParser :: Parser Options
runParser = OptRun <$> argument str mods <*> debugFlagParser
  where
    mods = fold [ metavar "TARGET"
                , help "Filepath of the source file."
                ]

runParserInfo :: ParserInfo Options
runParserInfo = info (helper <*> runParser) mods
  where
    mods = fold [ fullDesc
                , header "duo run - Run Duo source files"
                , progDesc "Run Duo source files."
                ]

---------------------------------------------------------------------------------
-- Commandline options for computing a dependency graph
---------------------------------------------------------------------------------

depsParser :: Parser Options
depsParser = OptDeps <$> argument str mods
  where
    mods = fold [ metavar "TARGET"
                , help "Filepath of the source file."
                ]

depsParserInfo :: ParserInfo Options
depsParserInfo = info (helper <*> depsParser) mods
  where
    mods = fold [ fullDesc
                , header "duo deps - Compute dependency graphs"
                , progDesc "Compute the dependency graph for a Duo module."
                ]

---------------------------------------------------------------------------------
-- Commandline option for showing the current version
---------------------------------------------------------------------------------

versionParser :: Parser Options
versionParser = OptVersion <$ flag' () (long "version" <> short 'v' <> help "Show version")

---------------------------------------------------------------------------------
-- Combined commandline parser
---------------------------------------------------------------------------------

commandParser :: Parser Options
commandParser = subparser $ fold [ command "run" runParserInfo
                                 , command "deps" depsParserInfo
                                 , command "lsp" lspParserInfo
                                 , command "check" typecheckParserInfo
                                 ]

optParser :: Parser Options
optParser = commandParser <|> versionParser

optParserInfo :: ParserInfo Options
optParserInfo = info (helper <*> optParser) mods
  where
    mods = fold [ fullDesc
                , progDesc "Duo is a research programming language focused on the study of dualities and subtyping."
                , header "duo - Typecheck, run and compile Duo programs"
                ]

---------------------------------------------------------------------------------
-- Exported Parser
---------------------------------------------------------------------------------

parseOptions :: IO Options
parseOptions = customExecParser p optParserInfo
  where
    p = prefs showHelpOnError
