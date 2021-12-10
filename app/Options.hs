module Options
  ( Options(..)
  , optParserInfo
  ) where

import Options.Applicative

data Options where
    OptRepl :: Options
    OptLSP :: Options
    OptCompile :: FilePath -> Options
    OptVersion :: Options

---------------------------------------------------------------------------------
-- Commandline options for starting a REPL
---------------------------------------------------------------------------------

replParser :: Parser Options
replParser = pure OptRepl

replParserInfo :: ParserInfo Options
replParserInfo = info (replParser <**> helper)
                      ( fullDesc 
                      <> header "dualsub repl - Start an interactive Repl"
                      )

---------------------------------------------------------------------------------
-- Commandline options for starting a LSP session
---------------------------------------------------------------------------------

lspParser :: Parser Options
lspParser = pure OptLSP

lspParserInfo :: ParserInfo Options
lspParserInfo = info (lspParser <**> helper)
                     ( fullDesc 
                     <> header "dualsub lsp - Start an LSP session"
                     <> progDesc "This command starts an LSP session. You should probably only use this if you are an editor or know precisely what you are doing."
                     )

---------------------------------------------------------------------------------
-- Commandline options for compiling source files
---------------------------------------------------------------------------------

compileParser :: Parser Options
compileParser = OptCompile <$> argument str (
                                        metavar "TARGET"
                                        <> help "Filepath of the source file."
                                        )

compileParserInfo :: ParserInfo Options
compileParserInfo = info (compileParser <**> helper)
                         (fullDesc <> progDesc "Compile DualSub source files"
                                   <> header "dualsub compile - ")

---------------------------------------------------------------------------------
-- Commandline option for showing the current version
---------------------------------------------------------------------------------

versionParser :: Parser Options
versionParser = pure OptVersion

versionParserInfo :: ParserInfo Options
versionParserInfo = info (versionParser <**> helper) 
                         (fullDesc <> progDesc "Show the version")

---------------------------------------------------------------------------------
-- Combined commandline parser
---------------------------------------------------------------------------------

optParser :: Parser Options
optParser = subparser (  command "repl" replParserInfo
                       <> command "lsp" lspParserInfo
                       <> command "compile" compileParserInfo
                       <> command "version" versionParserInfo
                       )

optParserInfo :: ParserInfo Options
optParserInfo = info (optParser <**> helper)
  (  fullDesc
  <> progDesc "DualSub is a research programming language focused on the study of dualities and subtyping."
  <> header "dualsub - typecheck, run and compile DualSub programs"
  )