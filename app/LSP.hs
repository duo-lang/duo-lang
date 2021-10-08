module LSP where

import Control.Monad (forM_, void)
import Control.Monad.IO.Class (liftIO, MonadIO)
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Language.LSP.VFS ( virtualFileText, VirtualFile )
import Language.LSP.Server
    ( runServer,
      notificationHandler,
      requestHandler,
      runLspT,
      sendNotification,
      type (<~>)(Iso, forward, backward),
      Handlers,
      LanguageContextEnv,
      LspT(LspT),
      MonadLsp,
      Options(..),
      ServerDefinition(..),
      getVirtualFile, publishDiagnostics, flushDiagnosticsBySource)
import Language.LSP.Types
    ( uriToFilePath,
      toNormalizedUri,
      Empty(Empty),
      Diagnostic(..),
      DiagnosticSeverity(DsError),
      ServerInfo(ServerInfo, _name, _version),
      Position(Position, _line, _character),
      Range(..),
      Message,
      NotificationMessage(NotificationMessage),
      ResponseError,
      Method(Initialize),
      SMethod(SWindowShowMessage, SInitialized, SExit, SShutdown,
              STextDocumentDidOpen, STextDocumentDidChange,
              STextDocumentDidClose),
      DidChangeTextDocumentParams(DidChangeTextDocumentParams),
      DidOpenTextDocumentParams(DidOpenTextDocumentParams),
      TextDocumentItem(TextDocumentItem),
      TextDocumentSyncKind(TdSyncIncremental),
      TextDocumentSyncOptions(TextDocumentSyncOptions, _openClose,
                              _change, _willSave, _willSaveWaitUntil, _save),
      VersionedTextDocumentIdentifier(VersionedTextDocumentIdentifier),
      MessageType(MtError, MtInfo, MtWarning),
      ShowMessageParams(ShowMessageParams),
      Uri,
      NormalizedUri, toNormalizedFilePath)
import System.Exit ( exitSuccess )
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Data.Version (showVersion)
import Data.Map (Map)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import qualified Data.SortedList as SL
import Data.Void ( Void )
import Data.Text (Text)
import TypeInference.GenerateConstraints.Definition
    ( InferenceMode(InferNominal) )
import TypeInference.InferProgram ( inferProgram )
import Text.Megaparsec
import Text.Megaparsec.Error
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Paths_dualsub (version)
import Errors ( LocatedError )
import Utils ( Located(Located), Loc(..) )
import Text.Megaparsec.Pos ( unPos, SourcePos(SourcePos), pos1, Pos )
import Pretty.Pretty ( ppPrint )
import Data.GraphViz.Attributes.Complete (SmoothType(RNG))
import Text.Megaparsec (PosState(pstateSourcePos))

runLSP :: IO ()
runLSP = void (runServer definition)

-- Server Configuration

data LSPConfig = MkLSPConfig

newtype LSPMonad a = MkLSPMonad { unLSPMonad :: LspT LSPConfig IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadUnliftIO, MonadLsp LSPConfig)

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
  , codeActionKinds = Nothing
  , documentOnTypeFormattingTriggerCharacters = Nothing
  , executeCommandCommands = Nothing
  , serverInfo = Just ServerInfo { _name = "dualsub-lsp", _version = Just (T.pack $ showVersion version) }
  }

definition :: ServerDefinition LSPConfig
definition = ServerDefinition
  { defaultConfig = MkLSPConfig
  , onConfigurationChange = \config _ -> pure config
  , doInitialize = \env _req -> pure $ Right env
  , staticHandlers = handlers
  , interpretHandler = \env -> Iso { forward = runLspT env . unLSPMonad, backward = liftIO }
  , options = serverOptions
  }

initialize :: LanguageContextEnv LSPConfig
           -> Message Initialize
           -> IO (Either ResponseError ())
initialize _ _ = return $ Right ()

-- All Handlers

handlers :: Handlers LSPMonad
handlers = mconcat [ initializedHandler
                   , exitHandler
                   , shutdownHandler
                   , didOpenHandler
                   , didChangeHandler
                   , didCloseHandler
                   ]

-- Initialization Handlers

initializedHandler :: Handlers LSPMonad
initializedHandler = notificationHandler SInitialized $ \_notif -> do
  let msg = "LSP Server for DualSub Initialized!"
  sendNotification SWindowShowMessage (ShowMessageParams MtInfo msg)

-- Exit + Shutdown Handlers

exitHandler :: Handlers LSPMonad
exitHandler = notificationHandler SExit $ \_notif -> do
  liftIO exitSuccess

shutdownHandler :: Handlers LSPMonad
shutdownHandler = requestHandler SShutdown $ \_re responder -> do
  let rsp = Right Empty
  responder rsp
  liftIO exitSuccess

-- File Open + Change + Close Handlers

didOpenHandler :: Handlers LSPMonad
didOpenHandler = notificationHandler STextDocumentDidOpen $ \notif -> do
  let (NotificationMessage _ _ (DidOpenTextDocumentParams (TextDocumentItem uri _ _ _))) = notif
  sendInfo $ "Opened file: " <> (T.pack $ show uri)
  publishErrors uri

didChangeHandler :: Handlers LSPMonad
didChangeHandler = notificationHandler STextDocumentDidChange $ \notif -> do
  let (NotificationMessage _ _ (DidChangeTextDocumentParams (VersionedTextDocumentIdentifier uri _) _)) = notif
  sendInfo $ "Changed file:" <> (T.pack $ show uri)
  publishErrors uri

didCloseHandler :: Handlers LSPMonad
didCloseHandler = notificationHandler STextDocumentDidClose $ \_notif -> do
  return ()

-- Publish diagnostics for File

-- | Transform a Megaparsec "SourcePos" to a LSP "Position".
-- Megaparsec and LSP's numbering conventions don't align!
posToPosition :: SourcePos -> Position
posToPosition (SourcePos _ line column) =
  Position { _line = unPos line - 1, _character = unPos column - 1}

-- | Convert the Loc that we use internally to LSP's Range type.
locToRange :: Loc -> Range
locToRange (Loc startPos endPos) =
  Range { _start = posToPosition startPos
        , _end   = posToPosition endPos
        }


getPosFromOffset :: Int ->  PosState Text -> Position
getPosFromOffset offset ps =
  let
    ps' = snd (reachOffset offset ps)
  in
    posToPosition (pstateSourcePos ps')

parseErrorToDiag :: ParseErrorBundle Text Void -> Diagnostic
parseErrorToDiag err@ParseErrorBundle { bundlePosState, bundleErrors } = do
  let offset = errorOffset (NE.head bundleErrors)
  let pos = getPosFromOffset offset bundlePosState
  let rng = Range pos pos
  let msg = T.pack $ errorBundlePretty err
  Diagnostic { _range = rng
             , _severity = Just DsError
             , _code = Nothing 
             , _source = Nothing 
             , _message = msg
             , _tags = Nothing
             , _relatedInformation = Nothing 
  }

errorToDiag :: LocatedError -> Diagnostic
errorToDiag (Located loc err) =
  let
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
  let diag = parseErrorToDiag err
  publishDiagnostics 42 uri Nothing (M.fromList ([(Just "TypeInference", SL.toSortedList ([diag]))]))

sendLocatedError :: NormalizedUri -> LocatedError -> LSPMonad ()
sendLocatedError uri le = do
  let diag = errorToDiag le
  publishDiagnostics 42 uri Nothing (M.fromList ([(Just "TypeInference", SL.toSortedList [diag])]))


publishErrors :: Uri -> LSPMonad ()
publishErrors uri = do
  flushDiagnosticsBySource 42 (Just "TypeInference")
  mfile <- getVirtualFile (toNormalizedUri uri)
  let vfile :: VirtualFile = maybe undefined id mfile
  let file = virtualFileText vfile
  let fp = case uriToFilePath uri of
                Nothing -> "fail"
                Just fp' -> fp'
  let decls = runFileParser fp programP file
  case decls of
    Left err -> do
      sendError "Parsing error!"
      sendParsingError (toNormalizedUri uri) err
    Right decls -> do
      let res = inferProgram decls InferNominal
      case res of
        Left err -> do
          sendLocatedError (toNormalizedUri uri) err
          sendError "Typeinference error!"
        Right _ -> do
          sendInfo $ "No errors in " <> T.pack fp <> "!"

sendInfo :: T.Text -> LSPMonad ()
sendInfo msg = sendNotification SWindowShowMessage (ShowMessageParams MtInfo msg)

sendWarning :: T.Text -> LSPMonad ()
sendWarning msg = sendNotification SWindowShowMessage (ShowMessageParams MtWarning  msg)

sendError :: T.Text -> LSPMonad ()
sendError msg = sendNotification SWindowShowMessage (ShowMessageParams MtError msg)
