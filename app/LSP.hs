module LSP where

import Data.Default
import Language.LSP.Server

runLSP :: IO ()
runLSP = runServer definition >> return ()

-- Server Configuration

type LspConfig = ()

type LspMonad = IO

definition :: ServerDefinition LspConfig
definition = ServerDefinition
  { defaultConfig = ()
  , onConfigurationChange = \_ _ -> Left "onConfigurationChange not implemented"
  , doInitialize = error "doInitialize not implemented"
  , staticHandlers = handlers
  , interpretHandler = \_ -> Iso id id
  , options = def
  }

handlers :: Handlers LspMonad
handlers = mconcat []