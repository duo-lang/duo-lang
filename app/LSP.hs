module LSP where

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
  , onConfigurationChange = \_ _ -> Left "onConfigurationChange not implemented"
  , doInitialize = initialize
  , staticHandlers = handlers
  , interpretHandler = \_ -> Iso id id
  , options = def
  }

initialize :: LanguageContextEnv LspConfig
           -> Message Initialize 
           -> IO (Either ResponseError ())
initialize _ _ = return $ Right ()

handlers :: Handlers LspMonad
handlers = mconcat []