{-# LANGUAGE TypeOperators #-}
module LSP.LSP where

import Control.Monad.IO.Class (liftIO)
import Data.List ( find )
import qualified Data.Map as M
import qualified Data.HashMap.Strict as Map
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
      type (<~>)(Iso, forward, backward),
      Handlers,
      LanguageContextEnv,
      Options(..),
      ServerDefinition(..),
      getVirtualFile, publishDiagnostics, flushDiagnosticsBySource, setupLogger)
import Language.LSP.Types
import System.Exit ( exitSuccess, ExitCode (ExitFailure), exitWith )
import Text.Megaparsec ( ParseErrorBundle(..) )
import Paths_dualsub (version)
import System.Log.Logger

import Syntax.CommonTerm
import Syntax.STerms hiding (Command)
import Syntax.Types
import Errors ( LocatedError )
import LSP.MegaparsecToLSP ( locToRange, parseErrorBundleToDiag, posToPosition )
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint, NamedRep (NamedRep) )
import Pretty.Program ()
import Syntax.Program
import TypeInference.Driver
import Utils ( Located(..), Loc(..))
import Translate.Focusing (isFocusedSTerm, focusSTerm)
import Eval.Eval ( EvalOrder(CBV) )
import LSP.Definition

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
runLSP = do
  setupLogger (Just "lsplog.txt") ["lspserver"] DEBUG
  debugM "lspserver" $ "Starting LSP Server"
  errCode <- runServer definition
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

---------------------------------------------------------------------------------
-- Provide CodeActions
---------------------------------------------------------------------------------

codeActionHandler :: Handlers LSPMonad
codeActionHandler = requestHandler STextDocumentCodeAction $ \req responder -> do
  let (RequestMessage _ _ _ (CodeActionParams _workDoneToken _partialResultToken ident@(TextDocumentIdentifier uri) range _context)) = req
  liftIO $ debugM "lspserver.codeActionHandler" ("Received codeAction request: " <> show uri <> " range: " <> show range)
  mfile <- getVirtualFile (toNormalizedUri uri)
  let vfile :: VirtualFile = maybe (error "Virtual File not present!") id mfile
  let file = virtualFileText vfile
  let fp = fromMaybe "fail" (uriToFilePath uri)
  let decls = runFileParser fp programP file
  case decls of
    Left _err -> do
      responder (Right (List []))
    Right decls -> do
      res <- liftIO $ inferProgramIO (DriverState (defaultInferenceOptions { infOptsLibPath = ["examples"]}) mempty) decls
      case res of
        Left _err -> do
          responder (Right (List []))
        Right env -> do
          responder (Right (generateCodeActions ident env))

generateCodeActions :: TextDocumentIdentifier -> Environment FreeVarName -> List (Command  |? CodeAction)
generateCodeActions ident env = do
  let unfocusedPrds = M.toList  $ M.filter (\(tm,_,_) -> not (isFocusedSTerm CBV tm)) $ prdEnv env
  List (take 1 $ generateCodeAction ident <$> unfocusedPrds)

generateCodeAction :: TextDocumentIdentifier -> (FreeVarName, (STerm Prd () FreeVarName, Loc, TypeScheme Pos)) -> Command |? CodeAction
generateCodeAction ident arg@(name, _)= InR $ CodeAction { _title = "Focus " <> name
                                                         , _kind = Just CodeActionQuickFix 
                                                         , _diagnostics = Nothing
                                                         , _isPreferred = Nothing
                                                         , _disabled = Nothing
                                                         , _edit = Just (generateEdit ident arg)
                                                           
                                                         , _command = Nothing
                                                         , _xdata = Nothing
                                                         }

generateEdit :: TextDocumentIdentifier ->  (FreeVarName, (STerm Prd () FreeVarName, Loc, TypeScheme Pos)) -> WorkspaceEdit
generateEdit (TextDocumentIdentifier uri) (name,(tm,loc,ty)) =
  let
    newDecl = NamedRep $ PrdDecl Recursive () name (Just ty) (createNamesSTerm (focusSTerm CBV tm))
    replacement = ppPrint newDecl
    edit = TextEdit {_range= locToRange loc, _newText= replacement }
  in 
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }
