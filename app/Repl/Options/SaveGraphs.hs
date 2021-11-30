module Repl.Options.SaveGraphs (saveOption) where

import Control.Monad.State ( MonadIO(liftIO), gets )
import Data.GraphViz
    ( isGraphvizInstalled, runGraphviz, GraphvizOutput(XDot, Jpeg) )
import Data.Text (Text)
import System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import System.FilePath ((</>), (<.>))

import Parser.Parser ( runInteractiveParser, termP )
import Pretty.TypeAutomata (typeAutToDot)
import Repl.Repl
    ( Option(..),
      Repl,
      ReplState(replEnv, typeInfOpts),
      prettyRepl)
import Syntax.Program ( IsRec(NonRecursive) )
import Syntax.CommonTerm ( PrdCnsRep(PrdRep) )
import TypeAutomata.Definition ( TypeAut', EdgeLabelNormal )
import TypeAutomata.Simplify
    (
      SimplifyTrace(..)
    )
import TypeInference.Driver
    ( execDriverM,
      DriverState(DriverState),
      inferSTermTraced,
      TypeInferenceTrace(..)
    )
import Utils

-- Save

saveCmd :: Text -> Repl ()
saveCmd s = do
  env <- gets replEnv
  opts <- gets typeInfOpts
  case runInteractiveParser (termP PrdRep) s of
      Right (tloc,loc) -> do
        let inferenceAction = fst <$> inferSTermTraced NonRecursive (Loc loc loc) "" PrdRep tloc
        traceEither <- liftIO $ execDriverM (DriverState opts env) inferenceAction
        case fst <$> traceEither of
          Right trace -> case (trace_automata trace) of
                             Just tr -> liftIO $ saveFromTrace "" tr
                             Nothing -> prettyRepl ("Enable simplification before trying to save graphs" :: String)
          Left _err -> return ()
      Left _err -> return ()

saveFromTrace :: String -> SimplifyTrace pol -> IO ()
saveFromTrace str trace = do
  saveGraph ("0_typeAut_"       <> str) (trace_typeAut        trace)
  saveGraph ("1_typeAutDet"     <> str) (trace_typeAutDet     trace)
  saveGraph ("2_typeAutDetAdms" <> str) (trace_typeAutDetAdms trace)
  saveGraph ("3_minTypeAut"     <> str) (trace_minTypeAut     trace)

saveGraph :: String -> TypeAut' EdgeLabelNormal f pol -> IO ()
saveGraph fileName aut = do
  let graphDir = "graphs"
  let fileUri = "  file://"
  let jpg = "jpg"
  let xdot = "xdot"
  dotInstalled <- isGraphvizInstalled
  if dotInstalled
    then do
      createDirectoryIfMissing True graphDir
      currentDir <- getCurrentDirectory
      _ <- runGraphviz (typeAutToDot aut) Jpeg           (graphDir </> fileName <.> jpg)
      _ <- runGraphviz (typeAutToDot aut) (XDot Nothing) (graphDir </> fileName <.> xdot)
      putStrLn (fileUri ++ currentDir </> graphDir </> fileName <.> jpg)
    else do
      putStrLn "Cannot generate graphs: graphviz executable not found in path."


saveOption :: Option
saveOption = Option
  { option_name = "save"
  , option_cmd = saveCmd
  , option_help = ["Save generated type automata to disk as jpgs."]
  , option_completer = Nothing
  }
