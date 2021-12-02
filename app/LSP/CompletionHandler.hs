module LSP.CompletionHandler (completionHandler) where

import Data.Text (Text)
import Language.LSP.Types
import Language.LSP.Server

import Syntax.Program
import LSP.Definition

completionHandler :: Handlers LSPMonad
completionHandler = requestHandler STextDocumentCompletion $ \req responder -> do
    let completionItem :: CompletionItem = CompletionItem
                            { _label = "tastytesty"
                            , _kind = Just CiText
                            , _tags = Nothing
                            , _detail = Nothing
                            , _documentation = Nothing
                            , _deprecated = Just False
                            , _preselect = Nothing
                            , _sortText = Nothing
                            , _filterText = Nothing
                            , _insertText = Nothing
                            , _insertTextFormat = Nothing
                            , _insertTextMode = Nothing
                            , _textEdit = Nothing
                            , _additionalTextEdits = Nothing
                            , _commitCharacters = Nothing
                            , _command = Nothing
                            , _xdata = Nothing
                            }
    responder (Right (InL (List [completionItem])))


-- hoverHandler :: Handlers LSPMonad
-- hoverHandler = 
--   let (RequestMessage _ _ _ (HoverParams (TextDocumentIdentifier uri) pos _workDone)) = req
--   liftIO $ debugM "lspserver.hoverHandler" ("Received hover request: " <> show uri)
--   MkLSPConfig ref <- getConfig 
--   cache <- liftIO $ readIORef ref
--   case M.lookup uri cache of
--     Nothing -> responder (Right Nothing)
--     Just cache -> responder (Right (lookupInHoverMap pos cache)