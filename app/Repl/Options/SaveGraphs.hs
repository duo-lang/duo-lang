module Repl.Options.SaveGraphs (saveOption) where

import Control.Monad.State ( MonadIO(liftIO), gets )
import Data.GraphViz
    ( isGraphvizInstalled, runGraphviz, GraphvizOutput(XDot, Jpeg) )
import Data.Text (Text)
import Data.Text qualified as T
import System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import System.FilePath ((</>), (<.>))

import Text.Megaparsec ( errorBundlePretty )
import Parser.Parser ( runInteractiveParser, termP )
import Pretty.Pretty ( ppPrint, PrettyAnn )
import Pretty.Program ()
import Pretty.TypeAutomata (typeAutToDot)
import Repl.Repl
    ( Option(..),
      Repl,
      ReplState(replEnv, typeInfOpts),
      prettyRepl,
      prettyText)
import Syntax.Program ( IsRec(NonRecursive) )
import Syntax.Types ( TypeScheme )
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
                             Just tr -> saveFromTrace tr (trace_resType trace)
                             Nothing -> prettyRepl ("Enable simplification before trying to save graphs" :: String)
          Left err2 -> saveParseError err2
      Left err2 -> saveParseError (errorBundlePretty err2)

saveFromTrace :: SimplifyTrace pol -> TypeScheme pol -> Repl ()
saveFromTrace trace tys = do
  saveGraphFiles "0_typeAut" (trace_typeAut trace)
  saveGraphFiles "1_typeAutDet" (trace_typeAutDet trace)
  saveGraphFiles "2_typeAutDetAdms" (trace_typeAutDetAdms trace)
  saveGraphFiles "3_minTypeAut" (trace_minTypeAut trace)
  prettyText (" :: " <> ppPrint tys)

saveParseError :: PrettyAnn a =>  a -> Repl ()
saveParseError e = do
  prettyText (T.unlines [ "STerm parsing error:", ppPrint e ])
                     

saveGraphFiles :: String -> TypeAut' EdgeLabelNormal f pol -> Repl ()
saveGraphFiles fileName aut = do
  let graphDir = "graphs"
  let fileUri = "  file://"
  let jpg = "jpg"
  let xdot = "xdot"
  dotInstalled <- liftIO $ isGraphvizInstalled
  if dotInstalled
    then do
      liftIO $ createDirectoryIfMissing True graphDir
      currentDir <- liftIO $ getCurrentDirectory
      _ <- liftIO $ runGraphviz (typeAutToDot aut) Jpeg (graphDir </> fileName <.> jpg)
      _ <- liftIO $ runGraphviz (typeAutToDot aut) (XDot Nothing) (graphDir </> fileName <.> xdot)
      prettyRepl (fileUri ++ currentDir </> graphDir </> fileName <.> jpg)
    else do
      prettyText "Cannot execute command: graphviz executable not found in path."


saveOption :: Option
saveOption = Option
  { option_name = "save"
  , option_cmd = saveCmd
  , option_help = ["Save generated type automata to disk as jpgs."]
  , option_completer = Nothing
  }
