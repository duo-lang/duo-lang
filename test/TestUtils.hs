module TestUtils where

import Data.Bifunctor (first)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import System.Directory (listDirectory)
import Text.Megaparsec (errorBundlePretty)

import Errors
import Parser.Parser
import Syntax.CommonTerm
import Syntax.Program
import Syntax.Terms
import TypeInference.Driver
import Utils ( Located(Located), defaultLoc )


getAvailableCounterExamples :: IO [FilePath]
getAvailableCounterExamples = do
  examples <- listDirectory "test/counterexamples/"
  return (("test/counterexamples/" ++) <$> examples)

getAvailableExamples :: FilePath -> IO [FilePath]
getAvailableExamples fp = do
  examples <- listDirectory fp
  return ((fp ++) <$> filter (\s -> head s /= '.') examples)

getParsedDeclarations :: FilePath -> IO (Either Error [Declaration Parsed])
getParsedDeclarations fp = do
  s <- T.readFile fp
  return (first (ParseError . T.pack . errorBundlePretty) (runFileParser fp programP s))

getEnvironment :: FilePath -> InferenceOptions -> IO (Either Error Environment)
getEnvironment fp infopts = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      res <- inferProgramIO (DriverState infopts mempty) decls
      case res of
        Right (env,_) -> return (Right env)
        Left (Located _ err) -> return (Left err)
    Left err -> return (Left err)

reParseDecl :: Declaration ext -> Declaration Parsed
reParseDecl (PrdCnsDecl _ rep isRec fv ts tm) = PrdCnsDecl defaultLoc rep isRec fv ts (createNamesSTerm tm)
reParseDecl (CmdDecl _ fv cmd) = CmdDecl defaultLoc fv (createNamesCommand cmd)
reParseDecl (DataDecl _ decl) = DataDecl defaultLoc decl
reParseDecl (ImportDecl _ mn) = ImportDecl defaultLoc mn
reParseDecl (SetDecl _ txt) = SetDecl defaultLoc txt
reParseDecl ParseErrorDecl = ParseErrorDecl

reParse :: Program ext -> Program Parsed
reParse = fmap reParseDecl