module LSP.JumpToDefHandler where

import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Language.LSP.Types
import Language.LSP.Server
import LSP.Definition
import LSP.MegaparsecToLSP
import System.Log.Logger

-- hoverHandler :: Handlers LSPMonad
-- hoverHandler = requestHandler STextDocumentHover $ \req responder ->  do
--   let (RequestMessage _ _ _ (HoverParams (TextDocumentIdentifier uri) pos _)) = req
--   liftIO $ debugM "lspserver.hoverHandler" ("Received hover request: " <> show uri <> " at: " <> show pos)
--   MkLSPConfig ref <- getConfig
--   cache <- liftIO $ readIORef ref
--   case M.lookup uri cache of
--     Nothing -> do
--       sendInfo ("Hover Cache not initialized for: " <> T.pack (show uri))
--       responder (Right Nothing)
--     Just cache -> responder (Right (lookupInHoverMap pos cache))


jumpToDefHandler :: Handlers LSPMonad
jumpToDefHandler = requestHandler STextDocumentDefinition $ \req responder -> do
    let (RequestMessage _ _ _ (DefinitionParams (TextDocumentIdentifier uri) pos _ _)) = req
    liftIO $ debugM "lspserver.JumpToDefHandler" ("Received definition request: " <> show uri <> " at: " <> show pos)
    responder (Right (InL (Location { _uri = undefined, _range = undefined})))
    
