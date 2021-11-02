module LSP.HoverHandler
  ( hoverHandler
  , updateHoverCache
  ) where

import Language.LSP.Types
    ( Hover(Hover),
      HoverContents(HoverContents),
      HoverParams(HoverParams),
      MarkupContent(MarkupContent),
      MarkupKind(MkPlainText),
      RequestMessage(RequestMessage),
      SMethod(STextDocumentHover),
      TextDocumentIdentifier(TextDocumentIdentifier), Position, Uri )
import Language.LSP.Server
    ( requestHandler, Handlers, getConfig )
import qualified Data.Map as M
import Data.List ( find )
import System.Log.Logger ( debugM )
import Pretty.Pretty ( ppPrint )
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import LSP.Definition ( LSPMonad, LSPConfig (MkLSPConfig) )
import LSP.MegaparsecToLSP ( lookupPos )
import Syntax.Program ( Environment(defEnv, prdEnv, cnsEnv, declEnv) )
import Syntax.Types ( Typ(TyNominal), PolarityRep (PosRep), DataDecl (data_name) )
import TypeTranslation ( translateType )
import Syntax.Types (Polarity(Pos))
import Data.Either (fromRight)
import Data.IORef (readIORef, modifyIORef)

---------------------------------------------------------------------------------
-- Handle Type on Hover
---------------------------------------------------------------------------------

hoverHandler :: Handlers LSPMonad
hoverHandler = requestHandler STextDocumentHover $ \req responder ->  do
  let (RequestMessage _ _ _ (HoverParams (TextDocumentIdentifier uri) pos _workDone)) = req
  liftIO $ debugM "lspserver.hoverHandler" ("Received hover request: " <> show uri)
  MkLSPConfig ref <- getConfig 
  cache <- liftIO $ readIORef ref
  case M.lookup uri cache of
    Nothing -> responder (Right Nothing)
    Just cache -> responder (Right (cache pos))
 

updateHoverCache :: Uri -> Environment -> LSPMonad ()
updateHoverCache uri env = do
  MkLSPConfig ref <- getConfig
  liftIO $ modifyIORef ref (M.insert uri (lookupHoverEnv env))
  
lookupHoverEnv :: Environment -> Position -> Maybe Hover
lookupHoverEnv env pos =
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



