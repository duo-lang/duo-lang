{-# LANGUAGE RecordWildCards #-}
module Main where

import System.Console.Repline hiding (Command)
import System.FilePath ((</>), (<.>))
import System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import Control.Monad.Reader
import Control.Monad.State

import Data.Char (isSpace)
import Data.List (isPrefixOf)
import qualified Data.Map as M
import Prettyprinter (Pretty)

import Syntax.Terms
import Syntax.Types
import Syntax.TypeGraph
import Utils
import Parser
import Pretty
import Eval
import GenerateConstraints
import SolveConstraints
import Determinize
import FlowAnalysis
import Minimize
import Subsume
import Target

import Data.GraphViz

------------------------------------------------------------------------------
-- Internal State of the Repl
------------------------------------------------------------------------------

data ReplState = ReplState
  { termEnv :: TermEnvironment
  , typeEnv :: TypeEnvironment
  }

initialReplState :: ReplState
initialReplState = ReplState { termEnv = M.empty, typeEnv = M.empty }

------------------------------------------------------------------------------
-- Repl Monad and helper functions
------------------------------------------------------------------------------

type ReplInner = StateT ReplState IO
type Repl a = HaskelineT ReplInner a

modifyTermEnv :: (TermEnvironment -> TermEnvironment) -> Repl ()
modifyTermEnv f = modify $ \rs@ReplState{..} -> rs { termEnv = f termEnv }

modifyTypeEnv :: (TypeEnvironment -> TypeEnvironment) -> Repl ()
modifyTypeEnv f = modify $ \rs@ReplState{..} -> rs { typeEnv = f typeEnv }

prettyRepl :: Pretty a => a -> Repl ()
prettyRepl s = liftIO $ putStrLn (ppPrint s)

fromRight :: Pretty err => Either err b -> Repl b
fromRight (Right b) = return b
fromRight (Left err) = prettyRepl err >> abort

parseRepl :: String -> EnvParser e a -> Environment e -> Repl a
parseRepl s p env = fromRight (runEnvParser p env s)

------------------------------------------------------------------------------
-- Command
------------------------------------------------------------------------------

cmd :: String -> Repl ()
cmd s = do
  env <- gets termEnv
  com <- parseRepl s commandP env
  case eval com of
    Right res -> prettyRepl res
    Left err -> prettyRepl err

------------------------------------------------------------------------------
-- Options
------------------------------------------------------------------------------

type_cmd :: String -> Repl ()
type_cmd s = do
  env <- gets termEnv
  t <- parseRepl s (termP Prd) env
  (typedTerm, css, uvars) <- fromRight $ generateConstraints t
  typeAut <- fromRight $ solveConstraints css uvars (typedTermToType typedTerm) (termPrdOrCns t)
  let
    typeAutDet0 = determinizeTypeAut typeAut
    typeAutDet = removeAdmissableFlowEdges typeAutDet0
    minTypeAut = minimizeTypeAut typeAutDet
    res = autToType minTypeAut
  prettyRepl (" :: " ++ ppPrint res)

show_cmd :: String -> Repl ()
show_cmd s = do
  termEnv <- gets termEnv
  typeEnv <- gets typeEnv
  case runEnvParser typeSchemeP typeEnv s of
    Right ty -> prettyRepl ty
    Left err1 -> case runEnvParser (termP Prd) termEnv s of
      Right t -> prettyRepl t
      Left err2 -> prettyRepl ("Type parsing error:\n" ++ ppPrint err1 ++
                               "Term parsing error:\n"++ ppPrint err2)

def_cmd :: String -> Repl ()
def_cmd s = do
  termEnv <- gets termEnv
  typeEnv <- gets typeEnv
  case runEnvParser typeDefinitionP typeEnv s of
    Right (v,ty) -> modifyTypeEnv (M.insert v ty)
    Left err1 -> case runEnvParser definitionP termEnv s of
      Right (v,t) -> modifyTermEnv (M.insert v t)
      Left err2 -> prettyRepl ("Type parsing error:\n" ++ ppPrint err1 ++
                               "Term parsing error:\n"++ ppPrint err2)

save_cmd :: String -> Repl ()
save_cmd s = do
  termEnv <- gets termEnv
  typeEnv <- gets typeEnv
  case runEnvParser typeSchemeP typeEnv s of
    Right ty -> do
      aut <- fromRight (typeToAut ty)
      saveGraphFiles "gr" aut
    Left err1 -> case runEnvParser (termP Prd) termEnv s of
      Right t -> do
        (typedTerm, css, uvars) <- fromRight (generateConstraints t)
        typeAut <- fromRight $ solveConstraints css uvars (typedTermToType typedTerm) (termPrdOrCns t)
        saveGraphFiles "0_typeAut" typeAut
        let typeAutDet = determinizeTypeAut typeAut
        saveGraphFiles "1_typeAutDet" typeAutDet
        let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
        saveGraphFiles "2_typeAutDetAdms" typeAutDetAdms
        let minTypeAut = minimizeTypeAut typeAutDetAdms
        saveGraphFiles "3_minTypeAut" minTypeAut
        let res = autToType minTypeAut
        prettyRepl (" :: " ++ ppPrint res)
      Left err2 -> prettyRepl ("Type parsing error:\n" ++ ppPrint err1 ++
                               "Term parsing error:\n"++ ppPrint err2)

saveGraphFiles :: String -> TypeAut -> Repl ()
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

bind_cmd :: String -> Repl ()
bind_cmd s = do
  env <- gets termEnv
  (v,t) <- parseRepl s bindingP env
  (typedTerm, css, uvars) <- fromRight (generateConstraints t)
  typeAut <- fromRight (solveConstraints css uvars (typedTermToType typedTerm) (termPrdOrCns t))
  let
    typeAutDet0 = determinizeTypeAut typeAut
    typeAutDet  = removeAdmissableFlowEdges typeAutDet0
    minTypeAut  = minimizeTypeAut typeAutDet
    resType     = autToType minTypeAut
  modifyTypeEnv (M.insert v resType)


sub_cmd :: String -> Repl ()
sub_cmd s = do
  env <- gets typeEnv
  (t1,t2) <- parseRepl s subtypingProblemP env
  case (typeToAutPol Pos t1, typeToAutPol Pos t2) of
    (Right aut1, Right aut2) -> prettyRepl $ isSubtype aut1 aut2
    _ -> case (typeToAutPol Neg t1, typeToAutPol Neg t2) of
        (Right aut1, Right aut2) -> prettyRepl $ isSubtype aut1 aut2
        -- TODO: Make this error message better
        _ -> prettyRepl "Invalid input. Either the types have non-matching polarities, they aren't polar at all or the covariance rule is violated."

simplify_cmd :: String -> Repl ()
simplify_cmd s = do
  env <- gets typeEnv
  ty <- parseRepl s typeSchemeP env
  aut <- fromRight (typeToAut ty)
  prettyRepl (autToType aut)

load_cmd :: String -> Repl ()
load_cmd s = do
  env <- gets termEnv
  defs <- liftIO $ readFile s
  env' <- parseRepl defs environmentP env
  modifyTermEnv (env' `M.union`)

reload_cmd :: String -> Repl ()
reload_cmd input = do
  let s = case (dropWhile isSpace input) of {"" -> "prg.txt"; s' -> s'}
  load_cmd s

------------------------------------------------------------------------------
-- Repl Configuration
------------------------------------------------------------------------------

completer :: String -> ReplInner [String]
completer s = do
  termEnv <- gets termEnv
  typeEnv <- gets typeEnv
  return $ filter (s `isPrefixOf`) (M.keys termEnv ++ M.keys typeEnv)

ini :: Repl ()
ini = do
  prettyRepl "Algebraic subtyping for structural Ouroboro.\nPress Ctrl+D to exit."
  loadStandardEnv

final :: Repl ExitDecision
final = prettyRepl "Goodbye!" >> return Exit

opts :: ReplOpts ReplInner
opts = ReplOpts
  { banner           = const (pure ">>> ")
  , command          = cmd
  , options          = [ ("type", type_cmd)
                       , ("show", show_cmd)
                       , ("def", def_cmd)
                       , ("save", save_cmd)
                       , ("load", load_cmd)
                       , ("bind", bind_cmd)
                       , ("sub", sub_cmd)
                       , ("reload", reload_cmd)
                       , ("simplify", simplify_cmd)
                       ]
  , prefix           = Just ':'
  , multilineCommand = Nothing
  , tabComplete      = Word0 completer
  , initialiser      = ini
  , finaliser        = final
  }

loadStandardEnv :: Repl ()
loadStandardEnv = load_cmd "prg.txt"

------------------------------------------------------------------------------
-- Run the Repl
------------------------------------------------------------------------------

main :: IO ()
main = runStateT (evalReplOpts opts) initialReplState >> return ()
