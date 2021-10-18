module LSP.LSP where

import Control.Monad (void)
import Control.Monad.IO.Class (liftIO, MonadIO)
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Data.List ( find )
import qualified Data.Map as M
import Data.Maybe ( fromMaybe )
import qualified Data.SortedList as SL
import Data.Text (Text)
import qualified Data.Text as T
import Data.Version (showVersion)
import Data.Void ( Void )
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
import System.Exit ( exitSuccess )
import Text.Megaparsec ( ParseErrorBundle(..) )
import Paths_dualsub (version)

import Syntax.CommonTerm
import Errors ( LocatedError )
import LSP.MegaparsecToLSP ( locToRange, parseErrorBundleToDiag, posToPosition )
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint )
import Syntax.Program
import TypeInference.Driver
import Utils ( Located(..), Loc(..))




---------------------------------------------------------------------------------
-- LSPMonad and Utility Functions
---------------------------------------------------------------------------------

data LSPConfig = MkLSPConfig

newtype LSPMonad a = MkLSPMonad { unLSPMonad :: LspT LSPConfig IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadUnliftIO, MonadLsp LSPConfig)

sendInfo :: T.Text -> LSPMonad ()
sendInfo msg = sendNotification SWindowShowMessage (ShowMessageParams MtInfo msg)

sendWarning :: T.Text -> LSPMonad ()
sendWarning msg = sendNotification SWindowShowMessage (ShowMessageParams MtWarning  msg)

sendError :: T.Text -> LSPMonad ()
sendError msg = sendNotification SWindowShowMessage (ShowMessageParams MtError msg)

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
  , codeActionKinds = Nothing
  , documentOnTypeFormattingTriggerCharacters = Nothing
  , executeCommandCommands = Nothing
  , serverInfo = Just ServerInfo { _name = "dualsub-lsp"
                                 , _version = Just (T.pack $ showVersion version)
                                 }
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

---------------------------------------------------------------------------------
-- Running the LSP Server
---------------------------------------------------------------------------------

runLSP :: IO ()
runLSP = void (runServer definition)

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
  responder (Right Empty)
  liftIO exitSuccess

-- CancelRequestHandler
cancelRequestHandler :: Handlers LSPMonad
cancelRequestHandler = notificationHandler SCancelRequest $ \_notif -> do
  return ()
  
-- File Open + Change + Close Handlers

didOpenHandler :: Handlers LSPMonad
didOpenHandler = notificationHandler STextDocumentDidOpen $ \notif -> do
  let (NotificationMessage _ _ (DidOpenTextDocumentParams (TextDocumentItem uri _ _ _))) = notif
  -- sendInfo $ "Opened file: " <> (T.pack $ show uri)
  -- TODO: Log this Info
  publishErrors uri

didChangeHandler :: Handlers LSPMonad
didChangeHandler = notificationHandler STextDocumentDidChange $ \notif -> do
  let (NotificationMessage _ _ (DidChangeTextDocumentParams (VersionedTextDocumentIdentifier uri _) _)) = notif
  -- sendInfo $ "Changed file:" <> (T.pack $ show uri)
  -- TODO: Log this info
  publishErrors uri

didCloseHandler :: Handlers LSPMonad
didCloseHandler = notificationHandler STextDocumentDidClose $ \_notif -> do
  return ()

-- Publish diagnostics for File

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
  let diag = parseErrorBundleToDiag err
  publishDiagnostics 42 uri Nothing (M.fromList ([(Just "TypeInference", SL.toSortedList diag)]))

sendLocatedError :: NormalizedUri -> LocatedError -> LSPMonad ()
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
      res <- liftIO $ inferProgramIO (DriverState (defaultInferenceOptions { infOptsLibPath = ["examples"]}) mempty) decls
      case res of
        Left err -> do
          sendLocatedError (toNormalizedUri uri) err
          -- sendError "Typeinference error!"
        Right _ -> do
          sendInfo $ "No errors in " <> T.pack fp <> "!"

---------------------------------------------------------------------------------
-- Handle Type on Hover
---------------------------------------------------------------------------------

hoverHandler :: Handlers LSPMonad
hoverHandler = requestHandler STextDocumentHover $ \req responder ->  do
  let (RequestMessage _ _ _ (HoverParams (TextDocumentIdentifier uri) pos _workDone)) = req
  mfile <- getVirtualFile (toNormalizedUri uri)
  let vfile :: VirtualFile = maybe (error "Virtual File not present!") id mfile
  let file = virtualFileText vfile
  let fp = fromMaybe "fail" (uriToFilePath uri)
  let decls = runFileParser fp programP file
  case decls of
    Left _err -> do
      responder (Left (ResponseError ParseError "Failed Parsing" Nothing))
    Right decls -> do
      res <- liftIO $ inferProgramIO (DriverState (defaultInferenceOptions { infOptsLibPath = ["examples"]}) mempty) decls
      case res of
        Left _err -> do
          responder (Left (ResponseError InternalError "Failed typchecking" Nothing))
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
  in
    case defres of
      Just (_,(_,_,ty)) -> Just (Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)
      Nothing -> case prdres of
        Just (_,(_,_,ty)) -> Just (Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)
        Nothing -> case cnsres of
          Just (_,(_,_,ty)) -> Just (Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)
          Nothing -> Nothing

      

lookupPos :: Position -> Loc -> Bool 
lookupPos (Position l _) (Loc begin end) =
  let
    (Position l1 _) = posToPosition  begin
    (Position l2 _) = posToPosition end 
  in
    l1 <= l && l <= l2

