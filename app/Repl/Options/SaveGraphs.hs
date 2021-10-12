module Repl.Options.SaveGraphs (saveOption) where

import Control.Monad.State ( MonadIO(liftIO), gets )
import Data.GraphViz
    ( isGraphvizInstalled, runGraphviz, GraphvizOutput(XDot, Jpeg) )
import Data.Text (Text)
import qualified Data.Text as T
import System.Directory (createDirectoryIfMissing, getCurrentDirectory)
import System.FilePath ((</>), (<.>))

import Text.Megaparsec ( errorBundlePretty )
import Parser.Parser ( runInteractiveParser, stermP, typeSchemeP )
import Pretty.Pretty ( ppPrint )
import Pretty.Program ()
import Pretty.TypeAutomata (typeAutToDot)
import Repl.Repl
    ( Option(..),
      Repl,
      ReplState(replEnv, typeInfOpts),
      prettyRepl,
      prettyText,
      fromRight )
import Syntax.Program ( IsRec(NonRecursive) )
import Syntax.STerms ( PrdCnsRep(PrdRep) )
import Syntax.Types ( PolarityRep(PosRep) )
import TypeAutomata.Definition ( TypeAut', EdgeLabelNormal )
import TypeAutomata.ToAutomaton (typeToAut)
import TypeInference.InferProgram (inferSTermTraced, TypeInferenceTrace(..))
import Utils

-- Save

saveCmd :: Text -> Repl ()
saveCmd s = do
  env <- gets replEnv
  opts <- gets typeInfOpts
  case runInteractiveParser (typeSchemeP PosRep) s of
    Right ty -> do
      aut <- fromRight (typeToAut ty)
      saveGraphFiles "gr" aut
    Left err1 -> case runInteractiveParser (stermP PrdRep) s of
      Right (tloc,loc) -> do
        trace <- fromRight $ inferSTermTraced NonRecursive (Loc loc loc) "" opts PrdRep tloc env
        saveGraphFiles "0_typeAut" (trace_typeAut trace)
        saveGraphFiles "1_typeAutDet" (trace_typeAutDet trace)
        saveGraphFiles "2_typeAutDetAdms" (trace_typeAutDetAdms trace)
        saveGraphFiles "3_minTypeAut" (trace_minTypeAut trace)
        prettyText (" :: " <> ppPrint (trace_resType trace))
      Left err2 -> prettyText (T.unlines [ "Type parsing error:"
                                         , ppPrint (errorBundlePretty err1)
                                         , "Term parsing error:"
                                         , ppPrint (errorBundlePretty err2) ])

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