module Repl (runRepl) where

import System.Console.Repline hiding (Command)
import System.Console.Haskeline.Completion
import System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import System.FilePath ((</>), (<.>))
import System.IO.Error(tryIOError)
import Control.Monad.Reader
import Control.Monad.State
import Data.GraphViz
import Data.List (isPrefixOf, find, intersperse)
import qualified Data.Map as M
import Data.Maybe (catMaybes)
import Prettyprinter (Pretty)

import Syntax.STerms
import Syntax.Types
import Syntax.TypeAutomaton
import Syntax.Program
import Parser.Parser
import Pretty.Pretty
import Pretty.TypeAutomata (typeAutToDot)
import Eval.Eval
import TypeAutomata.FromAutomaton (autToType)
import TypeAutomata.ToAutomaton (typeToAut)
import TypeAutomata.Subsume (isSubtype)
import TypeInference.InferTypes
import Translate.Translate (compile)
import Utils (trim)

------------------------------------------------------------------------------
-- Internal State of the Repl
------------------------------------------------------------------------------

data EvalSteps = Steps | NoSteps

data Mode = Symmetric | Asymmetric

data ReplState = ReplState
  { replEnv :: Environment
  , loadedFiles :: [FilePath]
  , steps :: EvalSteps
  , evalOrder :: EvalOrder
  , mode :: Mode
  }


initialReplState :: ReplState
initialReplState = ReplState { replEnv = mempty
                             , loadedFiles = []
                             , steps = NoSteps
                             , evalOrder = CBV
                             , mode = Symmetric
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

parseRepl ::Parser a -> String -> Repl a
parseRepl p s = do
  env <- gets replEnv
  fromRight (runEnvParser p env s)

safeRead :: FilePath -> Repl String
safeRead file =  do
  let file' = trim file
  res <- liftIO $ tryIOError (readFile file')
  case res of
    (Left _) -> do
      liftIO $ putStrLn $ "File with name " ++ file' ++ " does not exist."
      abort
    (Right s) -> return $ s

------------------------------------------------------------------------------
-- Command
------------------------------------------------------------------------------

cmd :: String -> Repl ()
cmd s = do
  mode <- gets mode
  case mode of
    Symmetric  -> cmdSymmetric  s
    Asymmetric -> cmdAsymmetric s


cmdSymmetric :: String -> Repl ()
cmdSymmetric s = do
  com <- parseRepl commandP s
  evalOrder <- gets evalOrder
  env <- gets replEnv
  steps <- gets steps
  case steps of
    NoSteps -> do
      res <- fromRight $ runEval (eval com) evalOrder env
      prettyRepl res
    Steps -> do
      res <- fromRight $ runEval (evalSteps com) evalOrder env
      forM_ res (\cmd -> prettyRepl cmd >> prettyRepl "----")

cmdAsymmetric :: String -> Repl ()
cmdAsymmetric s = do
  tm <- parseRepl atermP s
  evalOrder <- gets evalOrder
  env <- gets replEnv  
  let res = runEval (evalATermComplete tm) evalOrder env
  case res of
    Left error -> prettyRepl error
    Right res' -> prettyRepl res'
  

------------------------------------------------------------------------------
-- Options
------------------------------------------------------------------------------

data Option = Option
  { option_name :: String
  , option_cmd  :: String -> Repl ()
  , option_help :: [String]
  , option_completer :: Maybe (CompletionFunc ReplInner)
  }

-- Set & Unset

set_cmd_variants :: [(String, Repl ())]
set_cmd_variants = [ ("cbv", modify (\rs -> rs { evalOrder = CBV }))
                   , ("cbn", modify (\rs -> rs { evalOrder = CBV }))
                   , ("steps", modify (\rs -> rs { steps = Steps }))
                   , ("symmetric", modify (\rs -> rs { mode = Symmetric }))
                   , ("asymmetric", modify (\rs -> rs { mode = Asymmetric })) ]
set_cmd :: String -> Repl ()
set_cmd s = do
  let s' = trim s
  case lookup s' set_cmd_variants of
    Just action -> action
    Nothing -> do
      prettyRepl $ unlines [ "The option " ++ s' ++ " is not recognized."
                           , "Available options: " ++ concat (intersperse ", " (fst <$> set_cmd_variants))]

setCompleter :: CompletionFunc ReplInner
setCompleter = mkWordCompleter (x f)
  where
    f n = return $ filter (isPrefixOf n) (fst <$> set_cmd_variants)
    x f word = f word >>= return . map simpleCompletion

unsetCompleter :: CompletionFunc ReplInner
unsetCompleter = mkWordCompleter (x f)
  where
    f n = return $ filter (isPrefixOf n) (fst <$> unset_cmd_variants)
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

unset_cmd_variants :: [(String, Repl ())]
unset_cmd_variants = [ ("steps", modify (\rs -> rs { steps = NoSteps })) ]

unset_cmd :: String -> Repl ()
unset_cmd s = do
  let s' = trim s
  case lookup s' unset_cmd_variants of
    Just action -> action
    Nothing -> do
      prettyRepl $ unlines [ "The option " ++ s' ++ " is not recognized."
                           , "Available options: " ++ concat (intersperse ", " (fst <$> unset_cmd_variants))]

unset_option :: Option
unset_option = Option
  { option_name = "unset"
  , option_cmd = unset_cmd
  , option_help = ["Unset a Repl option."]
  , option_completer = Just unsetCompleter
  }

-- Type

type_cmd :: String -> Repl ()
type_cmd s = do
  env <- gets replEnv
  case runEnvParser (stermP PrdRep) env s of
    Right t -> do
      res <- fromRight $ inferSTerm PrdRep t env
      prettyRepl (" S :: " ++ ppPrint res)
    Left err1 -> do
      case runEnvParser atermP env s of
        Right t -> do
          res <- fromRight $ inferATerm t env
          prettyRepl (" A :: " ++ ppPrint res)
        Left err2 -> do
          prettyRepl "Cannot parse as sterm:"
          prettyRepl err1
          prettyRepl "Cannot parse as aterm:"
          prettyRepl err2

type_option :: Option
type_option = Option
  { option_name = "type"
  , option_cmd = type_cmd
  , option_help = ["Enter a producer term and show the inferred type."]
  , option_completer = Nothing
  }

-- Show

show_cmd :: String -> Repl ()
show_cmd s = do
  env <- gets replEnv
  case M.lookup s (prdEnv env) of
    Just prd -> prettyRepl prd
    Nothing -> case M.lookup s (cnsEnv env) of
      Just cns -> prettyRepl cns
      Nothing -> case M.lookup s (cmdEnv env) of
        Just cmd -> prettyRepl cmd
        Nothing -> case M.lookup s (defEnv env) of
          Just def -> prettyRepl def
          Nothing -> case M.lookup (MkTypeName s) (typEnv env) of
            Just typ -> prettyRepl typ
            Nothing -> prettyRepl "Not in environment."

show_option :: Option
show_option = Option
  { option_name = "show"
  , option_cmd = show_cmd
  , option_help = ["Display term or type on the command line."]
  , option_completer = Nothing
  }

-- Show TypeDeclaration

show_type_cmd :: String -> Repl ()
show_type_cmd s = do
  env <- gets (declEnv . replEnv)
  let maybeDecl = find (\x -> data_name x == MkTypeName s) env
  case maybeDecl of
    Nothing -> prettyRepl ("Type: " ++ s ++ " not found in environment.")
    Just decl -> prettyRepl decl
show_type_option :: Option
show_type_option = Option
  { option_name = "showtype"
  , option_cmd = show_type_cmd
  , option_help = ["Show the definition of a nominal type"]
  , option_completer = Nothing
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
  , option_completer = Nothing
  }

-- Save

save_cmd :: String -> Repl ()
save_cmd s = do
  env <- gets replEnv
  case runEnvParser typeSchemeP env s of
    Right ty -> do
      aut <- fromRight (typeToAut ty)
      saveGraphFiles "gr" aut
    Left err1 -> case runEnvParser (stermP PrdRep) env s of
      Right t -> do
        trace <- fromRight $ inferSTermTraced PrdRep t env
        saveGraphFiles "0_typeAut" (trace_typeAut trace)
        saveGraphFiles "1_typeAutDet" (trace_typeAutDet trace)
        saveGraphFiles "2_typeAutDetAdms" (trace_typeAutDetAdms trace)
        saveGraphFiles "3_minTypeAut" (trace_minTypeAut trace)
        prettyRepl (" :: " ++ ppPrint (trace_resType trace))
      Left err2 -> prettyRepl ("Type parsing error:\n" ++ ppPrint err1 ++
                               "Term parsing error:\n"++ ppPrint err2)

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
    False -> prettyRepl "Cannot execute command: graphviz executable not found in path."


save_option :: Option
save_option = Option
  { option_name = "save"
  , option_cmd = save_cmd
  , option_help = ["Save generated type automata to disk as jpgs."]
  , option_completer = Nothing
  }

-- Bind

bind_cmd :: String -> Repl ()
bind_cmd s = do
  env <- gets replEnv
  (v,t) <- parseRepl bindingP s
  resType <- fromRight $ inferSTerm PrdRep t env
  modifyEnvironment (insertDecl (TypDecl v resType))


bind_option :: Option
bind_option = Option
  { option_name = "bind"
  , option_cmd = bind_cmd
  , option_help = ["Infer the type of producer term, and add corresponding type declaration to environment."]
  , option_completer = Nothing
  }

-- Subsume

sub_cmd :: String -> Repl ()
sub_cmd s = do
  (t1,t2) <- parseRepl subtypingProblemP s
  aut1 <- fromRight (typeToAut t1)
  aut2 <- fromRight (typeToAut t2)
  prettyRepl $ isSubtype aut1 aut2


sub_option :: Option
sub_option = Option
  { option_name = "sub"
  , option_cmd = sub_cmd
  , option_help = [ "Check whether subsumption holds between two types. E.g."
                  , "\":sub {+ True +} <: {+ True, False +}\""]
  , option_completer = Nothing
  }

-- Simplify

simplify_cmd :: String -> Repl ()
simplify_cmd s = do
  ty <- parseRepl typeSchemeP s
  aut <- fromRight (typeToAut ty)
  prettyRepl (autToType aut)

simplify_option :: Option
simplify_option = Option
  { option_name = "simplify"
  , option_cmd = simplify_cmd
  , option_help = ["Simplify the given type."]
  , option_completer = Nothing
  }

-- Load

load_cmd :: String -> Repl ()
load_cmd s = do
  modifyLoadedFiles ((:) s)
  load_file s

load_file :: FilePath -> Repl ()
load_file s = do
  defs <- safeRead s
  newEnv <- parseRepl environmentP defs
  modifyEnvironment ((<>) newEnv)
  prettyRepl $ "Successfully loaded: " ++ s

load_option :: Option
load_option = Option
  { option_name = "load"
  , option_cmd = load_cmd
  , option_help = ["Load the given file from disk and add it to the environment."]
  , option_completer = Just fileCompleter
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
  , option_completer = Nothing
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
  , option_completer = Nothing
  }

-- Compile

compile_cmd :: String -> Repl ()
compile_cmd s = do
  env <- gets replEnv
  case runEnvParser (stermP PrdRep) env s of
    Right t -> do
      prettyRepl "Is an STerm, expected an ATerm:"
      prettyRepl (ppPrint t)
    Left err1 -> do
      case runEnvParser atermP env s of
        Right t -> do
            case compile t of
              Left  res -> do prettyRepl (" compile " ++ ppPrint t ++ "= " ++ ppPrint res)
              Right res -> do prettyRepl (" compile " ++ ppPrint t ++ "= " ++ ppPrint res)
        Left err2 -> do
          prettyRepl "Cannot parse as sterm:"
          prettyRepl err1
          prettyRepl "Cannot parse as aterm:"
          prettyRepl err2

compile_option :: Option
compile_option = Option
  { option_name = "compile"
  , option_cmd = compile_cmd
  , option_help = ["Enter a ATerm and show the translated STerm."]
  , option_completer = Nothing
  }
  
-- All Options

all_options :: [Option]
all_options = [ type_option, show_option, help_option, def_option, save_option, set_option, unset_option
              , sub_option, bind_option, simplify_option, compile_option, load_option, reload_option, show_type_option]

------------------------------------------------------------------------------
-- Repl Configuration
------------------------------------------------------------------------------

prefixCompleters :: [(String, CompletionFunc ReplInner)]
prefixCompleters = catMaybes (mkCompleter <$> all_options)
  where
    mkCompleter Option { option_completer = Nothing } = Nothing
    mkCompleter Option { option_name = name, option_completer = Just completer } = Just (':' : name, completer)

newCompleter :: CompleterStyle ReplInner
newCompleter = Prefix cmdCompleter prefixCompleters

cmdCompleter :: CompletionFunc ReplInner
cmdCompleter = mkWordCompleter (_simpleComplete f)
  where
    f n = do
      env <- gets replEnv
      let completionList = (':' :) . option_name <$> all_options
      let keys = concat [ M.keys (prdEnv env)
                        , M.keys (cnsEnv env)
                        , M.keys (cmdEnv env)
                        , M.keys (defEnv env)
                        , unTypeName <$> M.keys (typEnv env)
                        , (unTypeName . data_name) <$> (declEnv env)
                        ]
      return $ filter (isPrefixOf n) (completionList ++ keys)
    _simpleComplete f word = f word >>= return . map simpleCompletion

ini :: Repl ()
ini = do
  prettyRepl $ unlines [ "DualSub: Algebraic subtyping for data and codata."
                       , "Press Ctrl+D to exit."
                       , "Enter :help for a list of available commands."
                       ]
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
  , options          = (\opt -> (option_name opt, \s -> dontCrash ((option_cmd opt) s))) <$> all_options
  , prefix           = Just ':'
  , multilineCommand = Nothing
  , tabComplete      = newCompleter
  , initialiser      = ini
  , finaliser        = final
  }

------------------------------------------------------------------------------
-- Run the Repl
------------------------------------------------------------------------------

runRepl :: IO ()
runRepl = runStateT (evalReplOpts opts) initialReplState >> return ()

