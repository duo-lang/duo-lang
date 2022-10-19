module LSP.Handler.Various
  ( initializedHandler
  , exitHandler
  , shutdownHandler
  , cancelRequestHandler
  , didOpenHandler
  , didChangeHandler
  , didCloseHandler
  ) where

import Control.Monad.IO.Class ( liftIO )
import Language.LSP.Types qualified as LSP
import Language.LSP.Server qualified as LSP
import System.Exit ( exitSuccess ) 
import System.Log.Logger ( debugM )

import LSP.Definition ( LSPMonad, publishErrors )

---------------------------------------------------------------------------------
-- Initialized Notification Handler
--
-- https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#initialized
--
-- The initialized notification is sent from the client to the server after the
-- client received the result of the initialize request but before the client is
-- sending any other request or notification to the server. 
---------------------------------------------------------------------------------

initializedHandler :: LSP.Handlers LSPMonad
initializedHandler = LSP.notificationHandler LSP.SInitialized $ \_notif -> do
  liftIO $ debugM "lspserver" "LSP Server Initialized"

---------------------------------------------------------------------------------
-- Exit Notification Handler
--
-- https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#exit
--
-- A notification to ask the server to exit its process. The server should exit
-- with success code 0 if the shutdown request has been received before;
-- otherwise with error code 1.
---------------------------------------------------------------------------------

exitHandler :: LSP.Handlers LSPMonad
exitHandler = LSP.notificationHandler LSP.SExit $ \_notif -> do
  liftIO $ debugM "lspserver.exitHandler" "Received exit notification"
  liftIO exitSuccess

---------------------------------------------------------------------------------
-- Shutdown Request Handler
--
-- https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#shutdown
--
-- The shutdown request is sent from the client to the server. It asks the server
-- to shut down, but to not exit (otherwise the response might not be delivered
-- correctly to the client). There is a separate exit notification that asks the
-- server to exit. Clients must not send any notifications other than exit or
-- requests to a server to which they have sent a shutdown request. Clients
-- should also wait with sending the exit notification until they have received
-- a response from the shutdown request.
---------------------------------------------------------------------------------

shutdownHandler :: LSP.Handlers LSPMonad
shutdownHandler = LSP.requestHandler LSP.SShutdown $ \_re responder -> do
  liftIO $ debugM "lspserver.shutdownHandler" "Received shutdown request"
  responder (Right LSP.Empty)
  liftIO exitSuccess

---------------------------------------------------------------------------------
-- Cancel Request Notification Handler
--
-- https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#cancelRequest
--
---------------------------------------------------------------------------------

cancelRequestHandler :: LSP.Handlers LSPMonad
cancelRequestHandler = LSP.notificationHandler LSP.SCancelRequest $ \_notif -> do
  liftIO $ debugM "lspserver.cancelRequestHandler" "Received cancel request"
  return ()

---------------------------------------------------------------------------------
-- DidOpenTextDocument Notification Handler
--
-- https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_didOpen
--
-- The document open notification is sent from the client to the server to signal
-- newly opened text documents. The document’s content is now managed by the
-- client and the server must not try to read the document’s content using the
-- document’s Uri. Open in this sense means it is managed by the client. It
-- doesn’t necessarily mean that its content is presented in an editor. An open
-- notification must not be sent more than once without a corresponding close
-- notification send before. This means open and close notification must be
-- balanced and the max open count for a particular textDocument is one. Note
-- that a server’s ability to fulfill requests is independent of whether a text
-- document is open or closed.
---------------------------------------------------------------------------------

didOpenHandler :: LSP.Handlers LSPMonad
didOpenHandler = LSP.notificationHandler LSP.STextDocumentDidOpen $ \notif -> do
  let (LSP.NotificationMessage _ _ (LSP.DidOpenTextDocumentParams (LSP.TextDocumentItem uri _ _ _))) = notif
  liftIO $ debugM "lspserver.didOpenHandler" ("Opened file: " <> show uri)
  publishErrors uri

---------------------------------------------------------------------------------
-- DidChangeTextDocument Notification Handler
--
-- https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_didChange
--
-- he document change notification is sent from the client to the server to signal
-- changes to a text document. Before a client can change a text document it must
-- claim ownership of its content using the textDocument/didOpen notification. 
---------------------------------------------------------------------------------

didChangeHandler :: LSP.Handlers LSPMonad
didChangeHandler = LSP.notificationHandler LSP.STextDocumentDidChange $ \notif -> do
  let (LSP.NotificationMessage _ _ (LSP.DidChangeTextDocumentParams (LSP.VersionedTextDocumentIdentifier uri _) _)) = notif
  liftIO $ debugM "lspserver.didChangeHandler" ("Changed file: " <> show uri)
  publishErrors uri

---------------------------------------------------------------------------------
-- DidCloseTextDocument Notification Handler
--
-- https://microsoft.github.io/language-server-protocol/specifications/lsp/3.17/specification/#textDocument_didClose
--
-- The document close notification is sent from the client to the server when the
-- document got closed in the client. The document’s master now exists where the
-- document’s Uri points to (e.g. if the document’s Uri is a file Uri the master
-- now exists on disk). As with the open notification the close notification is
-- about managing the document’s content. Receiving a close notification doesn’t
-- mean that the document was open in an editor before. A close notification
-- requires a previous open notification to be sent. Note that a server’s ability
-- to fulfill requests is independent of whether a text document is open or closed.
---------------------------------------------------------------------------------

didCloseHandler :: LSP.Handlers LSPMonad
didCloseHandler = LSP.notificationHandler LSP.STextDocumentDidClose $ \notif -> do
  let (LSP.NotificationMessage _ _ (LSP.DidCloseTextDocumentParams uri)) = notif
  liftIO $ debugM "lspserver.didCloseHandler" ("Closed file: " <> show uri)
