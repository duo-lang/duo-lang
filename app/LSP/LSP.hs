{-# LANGUAGE TypeOperators #-}
module LSP.LSP ( runLSP ) where

import Data.IORef
import Control.Monad.Except (runExcept)
import Control.Monad.IO.Class (liftIO)
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as M
import Data.Maybe ( fromMaybe )
import Data.SortedList qualified as SL
import Data.Text qualified as T
import Data.Version (showVersion)
import Language.LSP.VFS ( virtualFileText )
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
import Paths_dualsub (version)
import System.Log.Logger ( Priority(DEBUG), debugM )

import Errors
import LSP.MegaparsecToLSP ( locToRange )
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint )
import Pretty.Program ()
import Driver.Driver
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

parserErrorToDiag :: ParserError -> Diagnostic
parserErrorToDiag (MkParserError loc msg) =
  Diagnostic { _range = locToRange loc
             , _severity = Just DsError
             , _code = Nothing
             , _source = Nothing
             , _message = msg
             , _tags = Nothing
             , _relatedInformation = Nothing
             }

errorToDiags :: Error -> [Diagnostic]
errorToDiags (ParserErrorBundle errs) = parserErrorToDiag <$> (NE.toList errs)
errorToDiags err = [diag]
  where
    diag = Diagnostic { _range = locToRange (maybe defaultLoc id (getLoc err))
                      , _severity = Just DsError
                      , _code = Nothing
                      , _source = Nothing
                      , _message = ppPrint err
                      , _tags = Nothing
                      , _relatedInformation = Nothing
                      }

sendLocatedError :: NormalizedUri -> Error -> LSPMonad ()
sendLocatedError uri le = do
  let diags = errorToDiags le
  publishDiagnostics 42 uri Nothing (M.fromList ([(Just "TypeInference", SL.toSortedList diags)]))


publishErrors :: Uri -> LSPMonad ()
publishErrors uri = do
  flushDiagnosticsBySource 42 (Just "TypeInference")
  mfile <- getVirtualFile (toNormalizedUri uri)
  case mfile of
    Nothing -> sendError "Virtual File not present!"
    Just vfile -> do
      let file = virtualFileText vfile
      let fp = fromMaybe "fail" (uriToFilePath uri)
      let decls = runExcept (runFileParser fp programP file)
      case decls of
        Left err -> do
          sendLocatedError (toNormalizedUri uri) err
        Right decls -> do
          res <- liftIO $ inferProgramIO (DriverState (defaultInferenceOptions { infOptsLibPath = ["examples"]}) mempty) decls
          case res of
            Left err -> do
              sendLocatedError (toNormalizedUri uri) err
            Right (env,_) -> do
              updateHoverCache uri env

