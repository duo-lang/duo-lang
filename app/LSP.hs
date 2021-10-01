module LSP where

import Control.Monad (forM_)
import Control.Monad.IO.Class (liftIO)
import Data.Default
import Language.LSP.Server
import Language.LSP.Types
import System.Exit ( exitSuccess )
import qualified Data.Text as T
import qualified Data.Text.IO as T

import TypeInference.GenerateConstraints.Definition
    ( InferenceMode(InferNominal) )
import TypeInference.InferProgram ( inferProgram )
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )

runLSP :: IO ()
runLSP = runServer definition >> return ()

-- Server Configuration

type LspConfig = ()

type LspMonad = IO

definition :: ServerDefinition LspConfig
definition = ServerDefinition
  { defaultConfig = ()
  , onConfigurationChange = const $ pure $ Right ()
  , doInitialize = \env _req -> pure $ Right env
  , staticHandlers = handlers
  , interpretHandler = \env -> Iso (runLspT env) liftIO
  , options = def
  }

initialize :: LanguageContextEnv LspConfig
           -> Message Initialize
           -> IO (Either ResponseError ())
initialize _ _ = return $ Right ()

-- All Handlers

handlers :: Handlers (LspM ())
handlers = mconcat [ initializedHandler
                   , exitHandler
                   , shutdownHandler
                   , didOpenHandler
                   , didChangeHandler
                   , didCloseHandler
                   ]

-- Initialization Handlers

initializedHandler :: Handlers (LspM ())
initializedHandler = notificationHandler SInitialized $ \_notif -> do
  let msg = "LSP Server for DualSub Initialized!"
  sendNotification SWindowShowMessage (ShowMessageParams MtInfo msg)

-- Exit + Shutdown Handlers

exitHandler :: Handlers (LspM ())
exitHandler = notificationHandler SExit $ \_notif -> do
  liftIO exitSuccess

shutdownHandler :: Handlers (LspM ())
shutdownHandler = requestHandler SShutdown $ \_re responder -> do
  let rsp = Right Empty
  responder rsp
  liftIO exitSuccess

-- File Open + Change + Close Handlers

didOpenHandler :: Handlers (LspM ())
didOpenHandler = notificationHandler STextDocumentDidOpen $ \notif -> do
  let (NotificationMessage _ _ (DidOpenTextDocumentParams (TextDocumentItem uri _ _ _))) = notif
  sendInfo $ "Opened file: " <> (T.pack $ show uri)
  forM_ (uriToFilePath uri) publishErrors

didChangeHandler :: Handlers (LspM ())
didChangeHandler = notificationHandler STextDocumentDidChange $ \notif -> do
  let (NotificationMessage _ _ (DidChangeTextDocumentParams (VersionedTextDocumentIdentifier uri _) _)) = notif
  sendInfo $ "Changed file:" <> (T.pack $ show uri)
  forM_ (uriToFilePath uri) publishErrors

didCloseHandler :: Handlers (LspM ())
didCloseHandler = notificationHandler STextDocumentDidClose $ \_notif -> do
  return ()

-- Publish diagnostics for File

publishErrors :: FilePath -> LspM LspConfig ()
publishErrors fp = do
  file <- liftIO $ T.readFile fp
  let decls = runFileParser fp programP file
  case decls of
    Left _err -> do
      sendError "Parsing error!"
    Right decls -> do
      let res = inferProgram decls InferNominal
      case res of
        Left _err -> do
          sendError "Typeinference error!"
        Right _ -> do
          sendInfo $ "No errors in " <> T.pack fp <> "!"

sendInfo :: T.Text -> LspM LspConfig ()
sendInfo msg = sendNotification SWindowShowMessage (ShowMessageParams MtInfo msg)

sendWarning :: T.Text -> LspM LspConfig ()
sendWarning msg = sendNotification SWindowShowMessage (ShowMessageParams MtWarning  msg)

sendError :: T.Text -> LspM LspConfig ()
sendError msg = sendNotification SWindowShowMessage (ShowMessageParams MtError msg)