module LSP.HoverHandler (hoverHandler) where

import Language.LSP.Types
    ( toNormalizedUri,
      uriToFilePath,
      Hover(Hover),
      HoverContents(HoverContents),
      HoverParams(HoverParams),
      Position(Position),
      MarkupContent(MarkupContent),
      MarkupKind(MkPlainText),
      RequestMessage(RequestMessage),
      SMethod(STextDocumentHover),
      TextDocumentIdentifier(TextDocumentIdentifier) )
import Language.LSP.Server
    ( getVirtualFile, requestHandler, Handlers )
import Language.LSP.VFS ( VirtualFile, virtualFileText )
import qualified Data.Map as M
import Data.List ( find )
import Data.Maybe ( fromMaybe )
import System.Log.Logger ( debugM )
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint )
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import LSP.Definition ( LSPMonad )
import LSP.MegaparsecToLSP ( posToPosition, lookupPos )
import Utils ( Loc(..) )
import Syntax.Program ( Environment(defEnv, prdEnv, cnsEnv, declEnv) )
import Syntax.CommonTerm ( FreeVarName )
import Syntax.Types ( Typ(TyNominal), PolarityRep (PosRep), DataDecl (data_name) )
import TypeInference.Driver
    ( defaultInferenceOptions,
      inferProgramIO,
      DriverState(DriverState),
      InferenceOptions(infOptsLibPath) )
import TypeTranslation ( translateType )
import Syntax.Types (Polarity(Pos))
import Data.Either (fromRight)

---------------------------------------------------------------------------------
-- Handle Type on Hover
---------------------------------------------------------------------------------

hoverHandler :: Handlers LSPMonad
hoverHandler = requestHandler STextDocumentHover $ \req responder ->  do
  let (RequestMessage _ _ _ (HoverParams (TextDocumentIdentifier uri) pos _workDone)) = req
  liftIO $ debugM "lspserver.hoverHandler" ("Received hover request: " <> show uri)
  mfile <- getVirtualFile (toNormalizedUri uri)
  let vfile :: VirtualFile = maybe (error "Virtual File not present!") id mfile
  let file = virtualFileText vfile
  let fp = fromMaybe "fail" (uriToFilePath uri)
  let decls = runFileParser fp programP file
  case decls of
    Left _err -> do
      responder (Right Nothing)
    Right decls -> do
      res <- liftIO $ inferProgramIO (DriverState (defaultInferenceOptions { infOptsLibPath = ["examples"]}) mempty) decls
      case res of
        Left _err -> do
          responder (Right Nothing)
        Right env -> do
          responder (Right (lookupHoverEnv pos env))

lookupHoverEnv :: Position -> Environment FreeVarName -> Maybe Hover
lookupHoverEnv pos env =
  let
    defs = M.toList (defEnv env)
    defres = find (\(_,(_,loc,_)) -> lookupPos pos loc) defs
    prds = M.toList (prdEnv env)
    prdres = find (\(_,(_,loc,_)) -> lookupPos pos loc) prds
    cnss = M.toList (cnsEnv env)
    cnsres = find (\(_,(_,loc,_)) -> lookupPos pos loc) cnss
    typs = find (\(loc,_) -> lookupPos pos loc) (declEnv env)
  in
    case defres of
      Just (_,(_,_,ty)) -> Just (Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)
      Nothing -> case prdres of
        Just (_,(_,_,ty)) -> Just (Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)
        Nothing -> case cnsres of
          Just (_,(_,_,ty)) -> Just (Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)
          Nothing -> case typs of
            Just (_,decl) ->
              let ty :: Typ Pos = fromRight (error "boom") (translateType env (TyNominal PosRep (data_name decl)))
              in Just (Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)
            Nothing -> Nothing



