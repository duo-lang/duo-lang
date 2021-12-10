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

replParser :: Parser Options
replParser = pure OptRepl

replParserInfo :: ParserInfo Options
replParserInfo = info (replParser <**> helper) fullDesc

lspParser :: Parser Options
lspParser = pure OptLSP

lspParserInfo :: ParserInfo Options
lspParserInfo = info (lspParser <**> helper) fullDesc

compileParser :: Parser Options
compileParser = OptCompile <$> strOption ( long "filepath" <> metavar "TARGET" <> help "foo")

compileParserInfo :: ParserInfo Options
compileParserInfo = info (compileParser <**> helper) fullDesc

versionParser :: Parser Options
versionParser = pure OptVersion

versionParserInfo :: ParserInfo Options
versionParserInfo = info (versionParser <**> helper) fullDesc

optParser :: Parser Options
optParser = hsubparser (  command "repl" replParserInfo
                       <> command "lsp" lspParserInfo
                       <> command "compile" compileParserInfo
                       <> command "version" versionParserInfo
                       )

optParserInfo :: ParserInfo Options
optParserInfo = info (optParser <**> helper)
  (  fullDesc
  <> progDesc "DualSub"
  <> header "dualsub - run, compile and check DualSub programs"
  )