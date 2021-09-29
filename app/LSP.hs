module LSP where

import Control.Monad.IO.Class (liftIO)
import Data.Default
import Language.LSP.Server
import Language.LSP.Types

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

handlers :: Handlers (LspM ())
handlers = mconcat [initializedHandler]

initializedHandler :: Handlers (LspM ())
initializedHandler = notificationHandler SInitialized $ \_notif -> do
  sendNotification SWindowShowMessage (ShowMessageParams MtInfo "Hello World")
