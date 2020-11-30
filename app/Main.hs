{-# LANGUAGE RecordWildCards #-}
module Main where

import System.Console.Repline hiding (Command)
import System.FilePath ((</>), (<.>))
import System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import Control.Monad.Reader
import Control.Monad.State

import Data.List (isPrefixOf)
import qualified Data.Map as M
import Prettyprinter (Pretty)

import Syntax.Terms
import Syntax.Types
import Syntax.TypeGraph
import Syntax.Program
import Parser
import Pretty
import Eval hiding (Environment)
import GenerateConstraints
import SolveConstraints
import TypeAutomata.Determinize
import TypeAutomata.FromAutomaton (autToType)
import TypeAutomata.FlowAnalysis
import TypeAutomata.Minimize (minimize)
import TypeAutomata.ToAutomaton (typeToAut, typeToAutPol)
import TypeAutomata.Subsume (isSubtype)


import Data.GraphViz

------------------------------------------------------------------------------
-- Internal State of the Repl
------------------------------------------------------------------------------

data ReplState = ReplState
  { replEnv :: Environment
  , loadedFiles :: [FilePath]
  }

initialReplState :: ReplState
initialReplState = ReplState { replEnv = mempty
                             , loadedFiles = ["prg.txt"]
                             }

------------------------------------------------------------------------------
-- Repl Monad and helper functions
------------------------------------------------------------------------------

type ReplInner = StateT ReplState IO
type Repl a = HaskelineT ReplInner a

modifyEnvironment :: (Environment -> Environment) -> Repl ()
modifyEnvironment f = modify $ \rs@ReplState{..} -> rs { replEnv = f replEnv }

modifyLoadedFiles :: ([FilePath] -> [FilePath]) -> Repl ()
modifyLoadedFiles f = modify $ \rs@ReplState{..} -> rs { loadedFiles = f loadedFiles }

prettyRepl :: Pretty a => a -> Repl ()
prettyRepl s = liftIO $ putStrLn (ppPrint s)

fromRight :: Pretty err => Either err b -> Repl b
fromRight (Right b) = return b
fromRight (Left err) = prettyRepl err >> abort

parseRepl :: String -> Parser a -> Environment -> Repl a
parseRepl s p env = fromRight (runEnvParser p env s)

------------------------------------------------------------------------------
-- Command
------------------------------------------------------------------------------

cmd :: String -> Repl ()
cmd s = do
  env <- gets replEnv
  com <- parseRepl s commandP env
  case eval com of
    Right res -> prettyRepl res
    Left err -> prettyRepl err

------------------------------------------------------------------------------
-- Options
------------------------------------------------------------------------------

data Option = Option
  { option_name :: String
  , option_cmd  :: String -> Repl ()
  , option_help :: [String]
  }

-- Type

type_cmd :: String -> Repl ()
type_cmd s = do
  env <- gets replEnv
  t <- parseRepl s (termP Prd) env
  (typedTerm, css, uvars) <- fromRight $ generateConstraints t
  typeAut <- fromRight $ solveConstraints css uvars (typedTermToType typedTerm) (termPrdOrCns t)
  let
    typeAutDet0 = determinize typeAut
    typeAutDet = removeAdmissableFlowEdges typeAutDet0
    minTypeAut = minimize typeAutDet
    res = autToType minTypeAut
  prettyRepl (" :: " ++ ppPrint res)

type_option :: Option
type_option = Option
  { option_name = "type"
  , option_cmd = type_cmd
  , option_help = ["Enter a producer term and show the inferred type."]
  }

-- Show

show_cmd :: String -> Repl ()
show_cmd s = do
  env <- gets replEnv
  case runEnvParser typeSchemeP env s of
    Right ty -> prettyRepl ty
    Left err1 -> case runEnvParser (termP Prd) env s of
      Right t -> prettyRepl t
      Left err2 -> prettyRepl $ unlines [ "Type parsing error:"
                                        , ppPrint err1
                                        , "Term parsing error:"
                                        , ppPrint err2
                                        ]

show_option :: Option
show_option = Option
  { option_name = "show"
  , option_cmd = show_cmd
  , option_help = ["Display term or type on the command line."]
  }

-- Define

def_cmd :: String -> Repl ()
def_cmd s = do
  env <- gets replEnv
  case runEnvParser declarationP env s of
    Right decl -> modifyEnvironment (insertDecl decl)
    Left err -> prettyRepl err

def_option :: Option
def_option = Option
  { option_name = "def"
  , option_cmd = def_cmd
  , option_help = [ "Add a declaration to the current environment. E.g."
                  , "\":def prd myTrue := {- Ap(x)[y] => x >> y -};\""]
  }

-- Save

save_cmd :: String -> Repl ()
save_cmd s = do
  env <- gets replEnv
  case runEnvParser typeSchemeP env s of
    Right ty -> do
      aut <- fromRight (typeToAut ty)
      saveGraphFiles "gr" aut
    Left err1 -> case runEnvParser (termP Prd) env s of
      Right t -> do
        (typedTerm, css, uvars) <- fromRight (generateConstraints t)
        typeAut <- fromRight $ solveConstraints css uvars (typedTermToType typedTerm) (termPrdOrCns t)
        saveGraphFiles "0_typeAut" typeAut
        let typeAutDet = determinize typeAut
        saveGraphFiles "1_typeAutDet" typeAutDet
        let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
        saveGraphFiles "2_typeAutDetAdms" typeAutDetAdms
        let minTypeAut = minimize typeAutDetAdms
        saveGraphFiles "3_minTypeAut" minTypeAut
        let res = autToType minTypeAut
        prettyRepl (" :: " ++ ppPrint res)
      Left err2 -> prettyRepl ("Type parsing error:\n" ++ ppPrint err1 ++
                               "Term parsing error:\n"++ ppPrint err2)

saveGraphFiles :: String -> TypeAut' EdgeLabel f -> Repl ()
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
    False -> prettyRepl "Cannot execute command: graphviz executable not found in path."


save_option :: Option
save_option = Option
  { option_name = "save"
  , option_cmd = save_cmd
  , option_help = ["Save generated type automata to disk as jpgs."]
  }

-- Bind

bind_cmd :: String -> Repl ()
bind_cmd s = do
  env <- gets replEnv
  (v,t) <- parseRepl s bindingP env
  (typedTerm, css, uvars) <- fromRight (generateConstraints t)
  typeAut <- fromRight (solveConstraints css uvars (typedTermToType typedTerm) (termPrdOrCns t))
  let
    typeAutDet0 = determinize typeAut
    typeAutDet  = removeAdmissableFlowEdges typeAutDet0
    minTypeAut  = minimize typeAutDet
    resType     = autToType minTypeAut
  modifyEnvironment (insertDecl (TypDecl v resType))


bind_option :: Option
bind_option = Option
  { option_name = "bind"
  , option_cmd = bind_cmd
  , option_help = ["Infer the type of producer term, and add corresponding type declaration to environment."]
  }

-- Subsume

sub_cmd :: String -> Repl ()
sub_cmd s = do
  env <- gets replEnv
  (t1,t2) <- parseRepl s subtypingProblemP env
  case (typeToAutPol Pos t1, typeToAutPol Pos t2) of
    (Right aut1, Right aut2) -> prettyRepl $ isSubtype aut1 aut2
    _ -> case (typeToAutPol Neg t1, typeToAutPol Neg t2) of
        (Right aut1, Right aut2) -> prettyRepl $ isSubtype aut1 aut2
        -- TODO: Make this error message better
        _ -> prettyRepl "Invalid input. Either the types have non-matching polarities, they aren't polar at all or the covariance rule is violated."

sub_option :: Option
sub_option = Option
  { option_name = "sub"
  , option_cmd = sub_cmd
  , option_help = [ "Check whether subsumption holds between two types. E.g."
                  , "\":sub {+ True +} <: {+ True, False +}\""]
  }

-- Simplify

simplify_cmd :: String -> Repl ()
simplify_cmd s = do
  env <- gets replEnv
  ty <- parseRepl s typeSchemeP env
  aut <- fromRight (typeToAut ty)
  prettyRepl (autToType aut)

simplify_option :: Option
simplify_option = Option
  { option_name = "simplify"
  , option_cmd = simplify_cmd
  , option_help = ["Simplify the given type."]
  }

-- Load

load_cmd :: String -> Repl ()
load_cmd s = do
  modifyLoadedFiles ((:) s)
  load_file s

load_file :: FilePath -> Repl ()
load_file s = do
  env <- gets replEnv
  defs <- liftIO $ readFile s
  newEnv <- parseRepl defs environmentP env
  modifyEnvironment ((<>) newEnv)
  prettyRepl $ "Successfully loaded: " ++ s

load_option :: Option
load_option = Option
  { option_name = "load"
  , option_cmd = load_cmd
  , option_help = ["Load the given file from disk and add it to the environment."]
  }

-- Reload

reload_cmd :: String -> Repl ()
reload_cmd "" = do
  loadedFiles <- gets loadedFiles
  forM_ loadedFiles load_file
reload_cmd _ = prettyRepl ":reload does not accept arguments"

reload_option :: Option
reload_option = Option
  { option_name = "reload"
  , option_cmd = reload_cmd
  , option_help = ["Reload all loaded files from disk."]
  }

-- Help

help_cmd :: String -> Repl ()
help_cmd _ = do
  prettyRepl "Available commands:\n"
  forM_ all_options (\opt -> showHelp (option_name opt) (option_help opt))
  where
    showHelp :: String -> [String] -> Repl ()
    showHelp name help = do
      prettyRepl $ ":" ++ name
      forM_ help (\help -> prettyRepl $ "    " ++ help)

help_option :: Option
help_option = Option
  { option_name = "help"
  , option_cmd = help_cmd
  , option_help = ["Show all available commands."]
  }

-- All Options

all_options :: [Option]
all_options = [ type_option, show_option, help_option, def_option, save_option
              , sub_option, bind_option, simplify_option, load_option, reload_option]

------------------------------------------------------------------------------
-- Repl Configuration
------------------------------------------------------------------------------

completer :: String -> ReplInner [String]
completer s = do
  env <- gets replEnv
  return $ filter (s `isPrefixOf`) (M.keys (prdEnv env) ++ M.keys (cnsEnv env) ++ M.keys (typEnv env))

ini :: Repl ()
ini = do
  prettyRepl "Algebraic subtyping for structural Ouroboro.\nPress Ctrl+D to exit."
  reload_cmd ""

final :: Repl ExitDecision
final = prettyRepl "Goodbye!" >> return Exit

repl_banner :: a -> Repl String
repl_banner _ = do
  loadedFiles <- gets loadedFiles
  pure (unwords loadedFiles ++ ">")

opts :: ReplOpts ReplInner
opts = ReplOpts
  { banner           = repl_banner
  , command          = cmd
  , options          = (\opt -> (option_name opt, option_cmd opt)) <$> all_options
  , prefix           = Just ':'
  , multilineCommand = Nothing
  , tabComplete      = Word0 completer
  , initialiser      = ini
  , finaliser        = final
  }

------------------------------------------------------------------------------
-- Run the Repl
------------------------------------------------------------------------------

main :: IO ()
main = runStateT (evalReplOpts opts) initialReplState >> return ()
