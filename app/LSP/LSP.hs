{-# LANGUAGE TypeOperators #-}
module LSP.LSP ( runLSP ) where

import Data.IORef
import Control.Monad.IO.Class (liftIO)
import Data.Map qualified as M
import Data.Maybe ( fromMaybe )
import Data.SortedList qualified as SL
import Data.Text (Text)
import Data.Text qualified as T
import Data.Version (showVersion)
import Data.Void ( Void )
import Language.LSP.VFS ( virtualFileText, VirtualFile )
import Language.LSP.Server
    ( runServer,
      notificationHandler,
      requestHandler,
      runLspT,
      type (<~>)(Iso, forward, backward),
      Handlers,
      Options(..),
      ServerDefinition(..),
      getVirtualFile, publishDiagnostics, flushDiagnosticsBySource, setupLogger)
import Language.LSP.Types
import System.Exit ( exitSuccess, ExitCode (ExitFailure), exitWith )
import Text.Megaparsec ( ParseErrorBundle(..) )
import Paths_dualsub (version)
import System.Log.Logger ( Priority(DEBUG), debugM )

import Errors
import Syntax.Lowering.Program
import LSP.MegaparsecToLSP ( locToRange, parseErrorBundleToDiag )
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint )
import Pretty.Program ()
import TypeInference.Driver
import Utils
import LSP.Definition
import LSP.HoverHandler ( hoverHandler, updateHoverCache )
import LSP.CodeActionHandler ( codeActionHandler )
import LSP.CompletionHandler ( completionHandler )

---------------------------------------------------------------------------------
-- Static configuration of the LSP Server
---------------------------------------------------------------------------------

serverOptions :: Options
serverOptions = Options
  { textDocumentSync = Just TextDocumentSyncOptions { _openClose = Just True
                                                    , _change = Just TdSyncIncremental
                                                    , _willSave = Nothing
                                                    , _willSaveWaitUntil = Nothing
                                                    , _save = Nothing
                                                    }
  , completionTriggerCharacters = Nothing
  , completionAllCommitCharacters = Nothing
  , signatureHelpTriggerCharacters = Nothing
  , signatureHelpRetriggerCharacters = Nothing
  , codeActionKinds = Just [CodeActionQuickFix]
  , documentOnTypeFormattingTriggerCharacters = Nothing
  , executeCommandCommands = Nothing
  , serverInfo = Just ServerInfo { _name = "dualsub-lsp"
                                 , _version = Just (T.pack $ showVersion version)
                                 }
  }

definition :: IO (ServerDefinition LSPConfig)
definition = do
  initialCache <- newIORef M.empty 
  return ServerDefinition
    { defaultConfig = MkLSPConfig initialCache
    , onConfigurationChange = \config _ -> pure config
    , doInitialize = \env _req -> pure $ Right env
    , staticHandlers = handlers
    , interpretHandler = \env -> Iso { forward = runLspT env . unLSPMonad, backward = liftIO }
    , options = serverOptions
    }

---------------------------------------------------------------------------------
-- Running the LSP Server
---------------------------------------------------------------------------------

runLSP :: Maybe FilePath -> IO ()
runLSP mLogPath = do
  setupLogger mLogPath ["lspserver"] DEBUG
  debugM "lspserver" $ "Starting LSP Server"
  initialDefinition <- definition
  errCode <- runServer initialDefinition
  case errCode of
    0 -> exitSuccess
    i -> exitWith $ ExitFailure i


---------------------------------------------------------------------------------
-- Static Message Handlers
---------------------------------------------------------------------------------

-- All Handlers

handlers :: Handlers LSPMonad
handlers = mconcat [ initializedHandler
                   , exitHandler
                   , shutdownHandler
                   , didOpenHandler
                   , didChangeHandler
                   , didCloseHandler
                   , hoverHandler
                   , cancelRequestHandler
                   , codeActionHandler
                   , completionHandler
                   ]

-- Initialization Handlers

initializedHandler :: Handlers LSPMonad
initializedHandler = notificationHandler SInitialized $ \_notif -> do
  liftIO $ debugM "lspserver" "LSP Server Initialized"


-- Exit + Shutdown Handlers

exitHandler :: Handlers LSPMonad
exitHandler = notificationHandler SExit $ \_notif -> do
  liftIO $ debugM "lspserver.exitHandler" "Received exit notification"
  liftIO exitSuccess

shutdownHandler :: Handlers LSPMonad
shutdownHandler = requestHandler SShutdown $ \_re responder -> do
  liftIO $ debugM "lspserver.shutdownHandler" "Received shutdown request"
  responder (Right Empty)
  liftIO exitSuccess

-- CancelRequestHandler
cancelRequestHandler :: Handlers LSPMonad
cancelRequestHandler = notificationHandler SCancelRequest $ \_notif -> do
  liftIO $ debugM "lspserver.cancelRequestHandler" "Received cancel request"
  return ()
  
-- File Open + Change + Close Handlers

didOpenHandler :: Handlers LSPMonad
didOpenHandler = notificationHandler STextDocumentDidOpen $ \notif -> do
  let (NotificationMessage _ _ (DidOpenTextDocumentParams (TextDocumentItem uri _ _ _))) = notif
  liftIO $ debugM "lspserver.didOpenHandler" ("Opened file: " <> show uri)
  publishErrors uri

didChangeHandler :: Handlers LSPMonad
didChangeHandler = notificationHandler STextDocumentDidChange $ \notif -> do
  let (NotificationMessage _ _ (DidChangeTextDocumentParams (VersionedTextDocumentIdentifier uri _) _)) = notif
  liftIO $ debugM "lspserver.didChangeHandler" ("Changed file: " <> show uri)
  publishErrors uri

didCloseHandler :: Handlers LSPMonad
didCloseHandler = notificationHandler STextDocumentDidClose $ \notif -> do
  let (NotificationMessage _ _ (DidCloseTextDocumentParams uri)) = notif
  liftIO $ debugM "lspserver.didCloseHandler" ("Closed file: " <> show uri)

-- Publish diagnostics for File

errorToDiag :: Error -> Diagnostic
errorToDiag err =
  let
    loc = maybe defaultLoc id (getLoc err)
    msg = ppPrint err
    range = locToRange loc
  in
    Diagnostic { _range = range
               , _severity = Just DsError
               , _code = Nothing
               , _source = Nothing
               , _message = msg
               , _tags = Nothing
               , _relatedInformation = Nothing
               }

sendParsingError :: NormalizedUri -> ParseErrorBundle Text Void -> LSPMonad ()
sendParsingError uri err = do
  let diag = parseErrorBundleToDiag err
  publishDiagnostics 42 uri Nothing (M.fromList ([(Just "TypeInference", SL.toSortedList diag)]))

sendLocatedError :: NormalizedUri -> Error -> LSPMonad ()
sendLocatedError uri le = do
  let diag = errorToDiag le
  publishDiagnostics 42 uri Nothing (M.fromList ([(Just "TypeInference", SL.toSortedList [diag])]))


publishErrors :: Uri -> LSPMonad ()
publishErrors uri = do
  flushDiagnosticsBySource 42 (Just "TypeInference")
  mfile <- getVirtualFile (toNormalizedUri uri)
  let vfile :: VirtualFile = maybe (error "Virtual File not present!") id mfile
  let file = virtualFileText vfile
  let fp = fromMaybe "fail" (uriToFilePath uri)
  let decls = runFileParser fp programP file
  case decls of
    Left err -> do
      -- sendError "Parsing error!"
      sendParsingError (toNormalizedUri uri) err
    Right decls -> do
      case lowerProgram decls of
        Left err -> sendLocatedError (toNormalizedUri uri) (OtherError Nothing (T.pack (show err)))
        Right decls -> do
          res <- liftIO $ inferProgramIO (DriverState (defaultInferenceOptions { infOptsLibPath = ["examples"]}) mempty) decls
          case res of
            Left err -> do
              sendLocatedError (toNormalizedUri uri) err
              -- sendError "Typeinference error!"
            Right (env,_) -> do
              updateHoverCache uri env
              sendInfo $ "No errors in " <> T.pack fp <> "!"

