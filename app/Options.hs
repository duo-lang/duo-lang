module Options
  ( Options(..)
  , parseOptions
  ) where

import Data.Foldable (fold)
import Options.Applicative

data Options where
    OptRepl :: Options
    OptLSP :: Maybe FilePath -> Options
    OptCompile :: FilePath -> Options
    OptVersion :: Options

---------------------------------------------------------------------------------
-- Commandline options for starting a REPL
---------------------------------------------------------------------------------

replParser :: Parser Options
replParser = pure OptRepl

replParserInfo :: ParserInfo Options
replParserInfo = info (helper <*> replParser) mods
  where
    mods = fold [ fullDesc
                , header "dualsub repl - Start an interactive REPL"
                , progDesc "Start an interactive REPL."
                ]
    

---------------------------------------------------------------------------------
-- Commandline options for starting a LSP session
---------------------------------------------------------------------------------

lspParser :: Parser Options
lspParser = OptLSP <$> (optional $ strOption mods)
  where
    mods = fold [ long "logfile"
                , short 'l'
                , metavar "FILE"
                ]


lspParserInfo :: ParserInfo Options
lspParserInfo = info (helper <*> lspParser) mods
  where
    mods = fold [ fullDesc
                , header "dualsub lsp - Start a LSP session"
                , progDesc "Start a LSP session. This command should only be invoked by editors or for debugging purposes."
                ]

---------------------------------------------------------------------------------
-- Commandline options for compiling source files
---------------------------------------------------------------------------------

compileParser :: Parser Options
compileParser = OptCompile <$> argument str mods
  where
    mods = fold [ metavar "TARGET"
                , help "Filepath of the source file."
                ]

compileParserInfo :: ParserInfo Options
compileParserInfo = info (helper <*> compileParser) mods
  where
    mods = fold [ fullDesc
                , header "dualsub compile - Compile DualSub source files"
                , progDesc "Compile DualSub source files."
                ]

---------------------------------------------------------------------------------
-- Commandline option for showing the current version
---------------------------------------------------------------------------------

versionParser :: Parser Options
versionParser = const OptVersion <$> flag' () (long "version" <> short 'v' <> help "Show version")

---------------------------------------------------------------------------------
-- Combined commandline parser
---------------------------------------------------------------------------------

commandParser :: Parser Options
commandParser = subparser $ fold [ command "repl" replParserInfo
                                 , command "compile" compileParserInfo
                                 , command "lsp" lspParserInfo
                                 ]

optParser :: Parser Options
optParser = commandParser <|> versionParser

optParserInfo :: ParserInfo Options
optParserInfo = info (helper <*> optParser) mods
  where
    mods = fold [ fullDesc
                , progDesc "DualSub is a research programming language focused on the study of dualities and subtyping."
                , header "dualsub - Typecheck, run and compile DualSub programs"
                ]

---------------------------------------------------------------------------------
-- Exported Parser
---------------------------------------------------------------------------------

parseOptions :: IO Options
parseOptions = customExecParser p optParserInfo
  where
    p = prefs showHelpOnError
