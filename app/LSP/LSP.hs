module LSP.LSP ( runLSP ) where

import Control.Monad.IO.Class (liftIO)
import Data.IORef ( newIORef )
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Version (showVersion)
import Language.LSP.Server qualified as LSP
import Language.LSP.Types qualified as LSP
import System.Exit ( exitSuccess, ExitCode (ExitFailure), exitWith )
import System.Log.Logger ( Priority(DEBUG), debugM )

import LSP.Definition ( LSPConfig(..), LSPMonad(unLSPMonad) )
import LSP.Handler.Hover ( hoverHandler )
import LSP.Handler.CodeAction ( codeActionHandler, evalHandler)
import LSP.Handler.Completion ( completionHandler )
import LSP.Handler.JumpToDef ( jumpToDefHandler )
import LSP.Handler.Various
    ( initializedHandler,
      exitHandler,
      shutdownHandler,
      cancelRequestHandler,
      didOpenHandler,
      didChangeHandler,
      didCloseHandler )
import Paths_duo_lang (version)

---------------------------------------------------------------------------------
-- Server Options
---------------------------------------------------------------------------------

serverOptions :: LSP.Options
serverOptions = LSP.Options
  { textDocumentSync = Just LSP.TextDocumentSyncOptions { _openClose = Just True
                                                        , _change = Just LSP.TdSyncIncremental
                                                        , _willSave = Nothing
                                                        , _willSaveWaitUntil = Nothing
                                                        , _save = Nothing
                                                        }
  , completionTriggerCharacters = Nothing
  , completionAllCommitCharacters = Nothing
  , signatureHelpTriggerCharacters = Nothing
  , signatureHelpRetriggerCharacters = Nothing
  , codeActionKinds = Just [LSP.CodeActionQuickFix]
  , documentOnTypeFormattingTriggerCharacters = Nothing
  , executeCommandCommands = Just ["duo-inline-eval","transformation-not-possible"]
  , serverInfo = Just LSP.ServerInfo { _name = "duo-lsp"
                                     , _version = Just (T.pack $ showVersion version)
                                     }
  }

---------------------------------------------------------------------------------
-- Server Definition with initial config
---------------------------------------------------------------------------------

definition :: IO (LSP.ServerDefinition LSPConfig)
definition = do
  initialCache <- newIORef M.empty
  return LSP.ServerDefinition
    { defaultConfig = MkLSPConfig initialCache
    , onConfigurationChange = \config _ -> pure config
    , doInitialize = \env _req -> pure $ Right env
    , staticHandlers = handlers
    , interpretHandler = \env -> LSP.Iso { forward = LSP.runLspT env . unLSPMonad, backward = liftIO }
    , options = serverOptions
    }

---------------------------------------------------------------------------------
-- Handlers
---------------------------------------------------------------------------------

handlers :: LSP.Handlers LSPMonad
handlers = mconcat [ initializedHandler
                   , exitHandler
                   , shutdownHandler
                   , didOpenHandler
                   , didChangeHandler
                   , didCloseHandler
                   , hoverHandler
                   , jumpToDefHandler
                   , cancelRequestHandler
                   , codeActionHandler
                   , completionHandler
                   , evalHandler
                   ]

---------------------------------------------------------------------------------
-- Running the LSP Server
---------------------------------------------------------------------------------

runLSP :: Maybe FilePath -> IO ()
runLSP mLogPath = do
  LSP.setupLogger mLogPath ["lspserver"] DEBUG
  debugM "lspserver" "Starting LSP Server"
  initialDefinition <- definition
  errCode <- LSP.runServer initialDefinition
  case errCode of
    0 -> exitSuccess
    i -> exitWith $ ExitFailure i
