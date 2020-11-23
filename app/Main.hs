{-# LANGUAGE OverloadedStrings #-}

module Main where

import System.Console.Repline hiding (Command)
import System.FilePath ((</>), (<.>))
import System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import Control.Monad.Reader
import Control.Monad.State
import Data.Bifunctor

import Data.Char (isSpace)
import Data.List (isPrefixOf)
import qualified Data.Map as M

import Syntax.Terms
import Syntax.Types
import Syntax.TypeGraph
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

--import Data.Graph.Inductive.Graph (prettyPrint)
import Data.GraphViz

type Repl = HaskelineT (StateT (TermEnvironment, TypeEnvironment) IO)

modifyTermEnv :: (TermEnvironment -> TermEnvironment) -> Repl ()
modifyTermEnv f = modify (bimap f id)

modifyTypeEnv :: (TypeEnvironment -> TypeEnvironment) -> Repl ()
modifyTypeEnv f = modify (bimap id f)

saveGraphFiles :: String -> TypeAut -> IO ()
saveGraphFiles fileName aut = do
  let graphDir = "graphs"
  let fileUri = "  file://"
  let jpg = "jpg"
  let xdot = "xdot"
  dotInstalled <- isGraphvizInstalled
  case dotInstalled of
    True -> do
      createDirectoryIfMissing True graphDir
      currentDir <- getCurrentDirectory
      _ <- runGraphviz (typeAutToDot aut) Jpeg (graphDir </> fileName <.> jpg)
      _ <- runGraphviz (typeAutToDot aut) (XDot Nothing) (graphDir </> fileName <.> xdot)
      putStrLn (fileUri ++ currentDir </> graphDir </> fileName <.> jpg)
    False -> putStrLn "Cannot execute command: graphviz executable not found in path."

cmd :: String -> Repl ()
cmd s = do
  (env,_) <- get
  case runEnvParser commandP env s of
    Right com -> case eval com of
      Right res -> liftIO $ putStrLn res
      Left err -> liftIO $ putStrLn (ppPrint err)
    Left err -> liftIO $ putStrLn (ppPrint err)

ini :: Repl ()
ini = do
  liftIO $ putStrLn "Algebraic subtyping for structural Ouroboro.\nPress Ctrl+D to exit."
  loadStandardEnv

final :: Repl ExitDecision
final = liftIO (putStrLn "Goodbye!") >> return Exit

type_cmd :: String -> Repl ()
type_cmd s = do
  (env,_) <- get
  case runEnvParser (termP Prd) env s of
    Right t -> case generateConstraints t of
      Right (typedTerm, css, uvars) -> case solveConstraints css uvars (typedTermToType typedTerm) (termPrdOrCns t) of
        Right typeAut -> let
            typeAutDet0 = determinizeTypeAut typeAut
            typeAutDet = removeAdmissableFlowEdges typeAutDet0
            minTypeAut = minimizeTypeAut typeAutDet
            res = autToType minTypeAut
          in
            liftIO $ putStrLn (" :: " ++ ppPrint res)
        Left err -> liftIO $ putStrLn (ppPrint err)
      Left err -> liftIO $ putStrLn (ppPrint err)
    Left err -> liftIO $ putStrLn (ppPrint err)

show_cmd :: String -> Repl ()
show_cmd s = do
  (termEnv,typeEnv) <- get
  case runEnvParser typeSchemeP typeEnv s of
    Right ty -> liftIO $ putStrLn (ppPrint ty)
    Left err1 -> case runEnvParser (termP Prd) termEnv s of
      Right t -> liftIO $ putStrLn (ppPrint t)
      Left err2 -> liftIO $ putStrLn ("Type parsing error:\n" ++ ppPrint err1 ++
                                      "Term pasrsing error:\n"++ ppPrint err2)

def_cmd :: String -> Repl ()
def_cmd s = do
  (termEnv,typeEnv) <- get
  case runEnvParser typeDefinitionP typeEnv s of
    Right (v,ty) -> modifyTypeEnv (M.insert v ty)
    Left err1 -> case runEnvParser definitionP termEnv s of
      Right (v,t) -> modifyTermEnv (M.insert v t)
      Left err2 -> liftIO $ putStrLn ("Type parsing error:\n" ++ ppPrint err1 ++
                                      "Term pasrsing error:\n"++ ppPrint err2)

save_cmd :: String -> Repl ()
save_cmd s = do
  (termEnv,typeEnv) <- get
  case runEnvParser typeSchemeP typeEnv s of
    Right ty -> case typeToAut ty of
      Right aut -> liftIO $ saveGraphFiles "gr" aut
      Left err -> liftIO $ putStrLn err
    Left err1 -> case runEnvParser (termP Prd) termEnv s of
      Right t -> case generateConstraints t of
        Right (typedTerm, css, uvars) -> case solveConstraints css uvars (typedTermToType typedTerm) (termPrdOrCns t) of
          Right typeAut -> do
              liftIO $ saveGraphFiles "0_typeAut" typeAut
              let typeAutDet = determinizeTypeAut typeAut
              liftIO $ saveGraphFiles "1_typeAutDet" typeAutDet
              let typeAutDetAdms  = removeAdmissableFlowEdges typeAutDet
              liftIO $ saveGraphFiles "2_typeAutDetAdms" typeAutDetAdms
              let minTypeAut = minimizeTypeAut typeAutDetAdms
              liftIO $ saveGraphFiles "3_minTypeAut" minTypeAut
              let res = autToType minTypeAut
              liftIO $ putStrLn (" :: " ++ ppPrint res)
          Left err -> liftIO $ putStrLn (ppPrint err)
        Left err -> liftIO $ putStrLn (ppPrint err)
      Left err2 -> liftIO $ putStrLn ("Type parsing error:\n" ++ ppPrint err1 ++
                                      "Term pasrsing error:\n"++ ppPrint err2)

bind_cmd :: String -> Repl ()
bind_cmd s = do
  (env,_) <- get
  case runEnvParser bindingP env s of
    Right (v,t) -> case generateConstraints t of
      Right (typedTerm, css, uvars) -> case solveConstraints css uvars (typedTermToType typedTerm) (termPrdOrCns t) of
        Right typeAut -> let
            typeAutDet0 = determinizeTypeAut typeAut
            typeAutDet = removeAdmissableFlowEdges typeAutDet0
            minTypeAut = minimizeTypeAut typeAutDet
            resType = autToType minTypeAut
          in
            modifyTypeEnv (M.insert v resType)
        Left err -> liftIO $ putStrLn (ppPrint err)
      Left err -> liftIO $ putStrLn (ppPrint err)
    Left err -> liftIO $ putStrLn (ppPrint err)

sub_cmd :: String -> Repl ()
sub_cmd s = do
  (_,env) <- get
  case runEnvParser subtypingProblemP env s of
    Right (t1, t2) -> case (typeToAutPol Pos t1, typeToAutPol Pos t2) of
      (Right aut1, Right aut2) -> liftIO $ putStrLn $ show (isSubtype aut1 aut2)
      _ -> case (typeToAutPol Neg t1, typeToAutPol Neg t2) of
        (Right aut1, Right aut2) -> liftIO $ putStrLn $ show (isSubtype aut1 aut2)
        -- TODO: Make this error message better
        _ -> liftIO $ putStrLn "Invalid input. Either the types have non-matching polarities, they aren't polar at all or the covariance rule is violated."
    Left err -> liftIO $ putStrLn (ppPrint err)

simplify_cmd :: String -> Repl ()
simplify_cmd s = do
  (_,env) <- get
  case runEnvParser typeSchemeP env s of
    Right ty -> case typeToAut ty of
      Right aut -> liftIO $ putStrLn (ppPrint (autToType aut))
      Left err -> liftIO $ putStrLn (ppPrint err)
    Left err -> liftIO $ putStrLn (ppPrint err)

load_cmd :: String -> Repl ()
load_cmd s = do
  (env,_) <- get
  defs <- liftIO $ readFile s
  case runEnvParser environmentP env defs of
    Right env' -> modifyTermEnv (env' `M.union`)
    Left err -> liftIO $ putStrLn (ppPrint err)

reload_cmd :: String -> Repl ()
reload_cmd input = do
  let s = case (dropWhile isSpace input) of {"" -> "prg.txt"; s' -> s'}
  load_cmd s

completer :: String -> StateT (TermEnvironment, TypeEnvironment) IO [String]
completer s = filter (s `isPrefixOf`) . uncurry (++) . bimap M.keys M.keys <$> get

opts :: ReplOpts (StateT (TermEnvironment, TypeEnvironment) IO)
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

{-
Right t = runEnvParser termP M.empty s
Right (ty,cs,uvs) = generateConstraints t
Right typeAut = solveConstraints cs uvs (typedTermToType ty) (termPrdOrCns t)
typeAutDet0 = determinizeTypeAut typeAut
typeAutDet = removeAdmissableFlowEdges typeAutDet0
minTypeAut = minimizeTypeAut typeAutDet
res = autToType minTypeAut
-}

main :: IO ()
main = runStateT (evalReplOpts opts) (M.empty, M.empty) >> return ()
