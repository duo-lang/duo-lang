module Repl.Options where

import Repl.Repl
import System.Console.Repline hiding (Command)
import System.Console.Haskeline.Completion
import System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import System.FilePath ((</>), (<.>))
import Control.Monad.Reader
import Control.Monad.State
import Data.GraphViz
import Data.List (isPrefixOf, find, intersperse)
import qualified Data.Map as M
import Data.Text (Text)
import qualified Data.Text as T

import Errors
import Syntax.STerms
import Syntax.Types
import TypeAutomata.Definition
import Syntax.Program
import Parser.Parser
import Pretty.Pretty
import Pretty.Errors (printLocatedError)
import Pretty.Program ()
import Pretty.TypeAutomata (typeAutToDot)
import Eval.Eval
import TypeAutomata.FromAutomaton (autToType)
import TypeAutomata.ToAutomaton (typeToAut)
import TypeAutomata.Subsume (subsume)
import Translate.Translate (compile)
import TypeInference.InferProgram (inferProgram, insertDeclIO, inferSTermTraced, TypeInferenceTrace(..))
import TypeInference.GenerateConstraints.Definition (InferenceMode(..))
import Utils (trim,  Verbosity(..))
import Text.Megaparsec (eof)

    -- Set & Unset

set_cmd_variants :: [(Text, Repl ())]
set_cmd_variants = [ ("cbv", modify (\rs -> rs { evalOrder = CBV }))
                   , ("cbn", modify (\rs -> rs { evalOrder = CBN }))
                   , ("steps", modify (\rs -> rs { steps = Steps }))
                   , ("verbose", modify (\rs -> rs { typeInfVerbosity = Verbose }))
                   , ("silent", modify (\rs -> rs { typeInfVerbosity = Silent }))
                   , ("symmetric", modify (\rs -> rs { mode = Symmetric }))
                   , ("asymmetric", modify (\rs -> rs { mode = Asymmetric }))
                   , ("refinements", modify (\rs -> rs { inferenceMode = InferRefined})) ]

set_cmd :: Text -> Repl ()
set_cmd s = do
  let s' = trim s
  case lookup s' set_cmd_variants of
    Just action -> action
    Nothing -> do
      prettyRepl $ T.unlines [ "The option " <> s' <> " is not recognized."
                             , "Available options: " <> T.concat (intersperse ", " (fst <$> set_cmd_variants))]

setCompleter :: CompletionFunc ReplInner
setCompleter = mkWordCompleter (x f)
  where
    f n = return $ filter (isPrefixOf n) (T.unpack . fst <$> set_cmd_variants)
    x f word = f word >>= return . map simpleCompletion

unsetCompleter :: CompletionFunc ReplInner
unsetCompleter = mkWordCompleter (x f)
  where
    f n = return $ filter (isPrefixOf n) (T.unpack . fst <$> unset_cmd_variants)
    x f word = f word >>= return . map simpleCompletion

mkWordCompleter :: Monad m =>  (String -> m [Completion]) -> CompletionFunc m
mkWordCompleter = completeWord (Just '\\') " \t()[]"

set_option :: Option
set_option = Option
  { option_name = "set"
  , option_cmd = set_cmd
  , option_help = ["Set a Repl option."]
  , option_completer = Just setCompleter
  }

unset_cmd_variants :: [(Text, Repl ())]
unset_cmd_variants = [ ("steps", modify (\rs -> rs { steps = NoSteps })) 
                     , ("refinements", modify (\rs -> rs { inferenceMode = InferNominal }))]

unset_cmd :: Text -> Repl ()
unset_cmd s = do
  let s' = trim s
  case lookup s' unset_cmd_variants of
    Just action -> action
    Nothing -> do
      prettyRepl $ T.unlines [ "The option " <> s' <> " is not recognized."
                             , "Available options: " <> T.concat (intersperse ", " (fst <$> unset_cmd_variants))]

unset_option :: Option
unset_option = Option
  { option_name = "unset"
  , option_cmd = unset_cmd
  , option_help = ["Unset a Repl option."]
  , option_completer = Just unsetCompleter
  }


-- Show

show_cmd :: Text -> Repl ()
show_cmd "" = do
  loadedFiles <- gets loadedFiles
  forM_ loadedFiles $ \fp -> do
    decls <- parseFile fp programP
    prettyRepl decls
show_cmd str = do
  let s = trim str
  env <- gets replEnv
  case M.lookup s (prdEnv env) of
    Just (prd,_) -> prettyRepl (NamedRep prd)
    Nothing -> case M.lookup s (cnsEnv env) of
      Just (cns,_) -> prettyRepl (NamedRep cns)
      Nothing -> case M.lookup s (cmdEnv env) of
        Just cmd -> prettyRepl (NamedRep cmd)
        Nothing -> case M.lookup s (defEnv env) of
          Just (def,_) -> prettyRepl (NamedRep def)
          Nothing -> prettyText "Not in environment."

show_option :: Option
show_option = Option
  { option_name = "show"
  , option_cmd = show_cmd
  , option_help = ["Display term or type on the command line."]
  , option_completer = Nothing
  }

-- Show TypeDeclaration

show_type_cmd :: Text -> Repl ()
show_type_cmd s = do
  env <- gets (declEnv . replEnv)
  let maybeDecl = find (\x -> data_name x == MkTypeName s) env
  case maybeDecl of
    Nothing -> prettyRepl ("Type: " <> s <> " not found in environment.")
    Just decl -> prettyRepl decl

show_type_option :: Option
show_type_option = Option
  { option_name = "showtype"
  , option_cmd = show_type_cmd
  , option_help = ["Show the definition of a nominal type"]
  , option_completer = Nothing
  }

-- Define

let_cmd :: Text -> Repl ()
let_cmd s = do
  decl <- fromRight (runInteractiveParser declarationP s)
  oldEnv <- gets replEnv
  verbosity <- gets typeInfVerbosity
  im <- gets inferenceMode
  newEnv <- liftIO $ insertDeclIO verbosity im decl oldEnv
  case newEnv of
    Nothing -> return ()
    Just newEnv -> modifyEnvironment (const newEnv)

let_option :: Option
let_option = Option
  { option_name = "let"
  , option_cmd = let_cmd
  , option_help = [ "Add a declaration to the current environment. E.g."
                  , "\":let prd myTrue := {- Ap(x)[y] => x >> y -};\""]
  , option_completer = Nothing
  }

-- Save

save_cmd :: Text -> Repl ()
save_cmd s = do
  env <- gets replEnv
  im <- gets inferenceMode
  case runInteractiveParser (typeSchemeP PosRep) s of
    Right ty -> do
      aut <- fromRight (typeToAut ty)
      saveGraphFiles "gr" aut
    Left err1 -> case runInteractiveParser (stermP PrdRep) s of
      Right (tloc,_) -> do
        trace <- fromRight $ inferSTermTraced NonRecursive "" im PrdRep tloc env
        saveGraphFiles "0_typeAut" (trace_typeAut trace)
        saveGraphFiles "1_typeAutDet" (trace_typeAutDet trace)
        saveGraphFiles "2_typeAutDetAdms" (trace_typeAutDetAdms trace)
        saveGraphFiles "3_minTypeAut" (trace_minTypeAut trace)
        prettyText (" :: " <> ppPrint (trace_resType trace))
      Left err2 -> prettyText (T.unlines [ "Type parsing error:"
                                         , ppPrint err1
                                         , "Term parsing error:"
                                         , ppPrint err2 ])

saveGraphFiles :: String -> TypeAut' EdgeLabelNormal f pol -> Repl ()
saveGraphFiles fileName aut = do
  let graphDir = "graphs"
  let fileUri = "  file://"
  let jpg = "jpg"
  let xdot = "xdot"
  dotInstalled <- liftIO $ isGraphvizInstalled
  case dotInstalled of
    True -> do
      liftIO $ createDirectoryIfMissing True graphDir
      currentDir <- liftIO $ getCurrentDirectory
      _ <- liftIO $ runGraphviz (typeAutToDot aut) Jpeg (graphDir </> fileName <.> jpg)
      _ <- liftIO $ runGraphviz (typeAutToDot aut) (XDot Nothing) (graphDir </> fileName <.> xdot)
      prettyRepl (fileUri ++ currentDir </> graphDir </> fileName <.> jpg)
    False -> prettyText "Cannot execute command: graphviz executable not found in path."


save_option :: Option
save_option = Option
  { option_name = "save"
  , option_cmd = save_cmd
  , option_help = ["Save generated type automata to disk as jpgs."]
  , option_completer = Nothing
  }

-- Subsume

sub_cmd :: Text -> Repl ()
sub_cmd s = do
  (t1,t2) <- parseInteractive subtypingProblemP s
  res <- fromRight (subsume t1 t2)
  prettyRepl res


sub_option :: Option
sub_option = Option
  { option_name = "sub"
  , option_cmd = sub_cmd
  , option_help = [ "Check whether subsumption holds between two types. E.g."
                  , "\":sub {+ True +} <: {+ True, False +}\""]
  , option_completer = Nothing
  }

-- Simplify

simplify_cmd :: Text -> Repl ()
simplify_cmd s = case go PosRep of 
                    Right pp -> pp
                    Left err -> case go NegRep of
                      Right pp -> pp
                      Left err' -> do
                        prettyRepl ("Parsing type failed" :: String)
                        prettyRepl ("Positive parsing error:" :: String)
                        prettyRepl err
                        prettyRepl ("Negative parsing error:" :: String)
                        prettyRepl err'
                        --  @prettyRepl String "Parsing type failed" 
                        --  @prettyRepl String "Positive parsing error:"
                        --  prettyRepl err
                        --  @prettyRepl String "Negative parsing error:"
                        --  prettyRepl err'
  where
    go :: forall p. PolarityRep p -> Either Error (Repl ())
    go rep = do
      ty <- runInteractiveParser (typeSchemeP rep <* eof) s
      aut <- typeToAut ty
      return $ prettyRepl (autToType aut)

simplify_option :: Option
simplify_option = Option
  { option_name = "simplify"
  , option_cmd = simplify_cmd
  , option_help = ["Simplify the given type."]
  , option_completer = Nothing
  }

-- Load

load_cmd :: Text -> Repl ()
load_cmd s = do
  let s' = T.unpack . trim $  s
  modifyLoadedFiles ((:) s')
  load_file s'

load_file :: FilePath -> Repl ()
load_file fp = do
  decls <- parseFile fp programP
  inferMode <- gets inferenceMode
  case inferProgram decls inferMode of
    Left err -> printLocatedError err
    Right newEnv -> do
      modifyEnvironment ((<>) newEnv)
      prettyRepl newEnv
      prettyRepl $ "Successfully loaded: " ++ fp

load_option :: Option
load_option = Option
  { option_name = "load"
  , option_cmd = load_cmd
  , option_help = ["Load the given file from disk and add it to the environment."]
  , option_completer = Just fileCompleter
  }

-- Reload

reload_cmd :: Text -> Repl ()
reload_cmd "" = do
  loadedFiles <- gets loadedFiles
  forM_ loadedFiles load_file
reload_cmd _ = prettyText ":reload does not accept arguments"

reload_option :: Option
reload_option = Option
  { option_name = "reload"
  , option_cmd = reload_cmd
  , option_help = ["Reload all loaded files from disk."]
  , option_completer = Nothing
  }



-- Compile

compile_cmd :: Text -> Repl ()
compile_cmd s = do
  case runInteractiveParser atermP s of
    Right (t, _pos) ->
      prettyText (" compile " <> ppPrint t <> "\n = " <> ppPrint (compile t))
    Left err2 -> do
      prettyText "Cannot parse as aterm:"
      prettyRepl err2

compile_option :: Option
compile_option = Option
  { option_name = "compile"
  , option_cmd = compile_cmd
  , option_help = ["Enter a ATerm and show the translated STerm."]
  , option_completer = Nothing
  }
