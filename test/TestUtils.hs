module TestUtils where

import Data.Text qualified as T
import Data.Text.IO qualified as T
import System.Directory (listDirectory)
import Text.Megaparsec (errorBundlePretty)

import Errors
import Parser.Parser
import Parser.Types (typP)
import Syntax.AST.Types (PolarityRep)
import Syntax.AST.Types qualified as AST
import Syntax.Lowering.Types
import Syntax.Lowering.Program
import Syntax.CommonTerm
import Syntax.AST.Program
import TypeInference.Driver

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
  case runFileParser fp programP s of
    Left err -> pure (Left (ParseError Nothing (T.pack (errorBundlePretty err))))
    Right prog -> do
      case lowerProgram prog of
        Left err -> pure (Left (OtherError Nothing err))
        Right prog -> pure (pure prog)
  

getEnvironment :: FilePath -> InferenceOptions -> IO (Either Error (Environment Inferred))
getEnvironment fp infopts = do
  decls <- getParsedDeclarations fp
  case decls of
    Right decls -> do
      fmap fst <$> inferProgramIO (DriverState infopts mempty) decls
    Left err -> return (Left err)


--- | Parse a type and lower it
typPLowering :: PolarityRep pol -> Parser (AST.Typ pol)
typPLowering rep = do
  t <- typP
  case lowerTyp rep t of
    Right t -> pure t
    Left err -> fail (show err)

-- | Parse a type scheme and lower it
typeSchemePLowering :: PolarityRep pol -> Parser (AST.TypeScheme pol)
typeSchemePLowering rep = do
  s <- typeSchemeP
  case lowerTypeScheme rep s of
    Right s -> pure s
    Left err -> fail (show err)