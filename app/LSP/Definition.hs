module LSP.Definition where

import Control.Monad.IO.Class ( MonadIO)
import Control.Monad.IO.Unlift (MonadUnliftIO)

import Data.IORef
import Language.LSP.Server
import Language.LSP.Types
import qualified Data.Text as T
---------------------------------------------------------------------------------
-- LSPMonad and Utility Functions
---------------------------------------------------------------------------------

type HoverCache = Position -> Maybe Hover
data LSPConfig = MkLSPConfig (IORef HoverCache)

newtype LSPMonad a = MkLSPMonad { unLSPMonad :: (LspT LSPConfig IO a) }
  deriving (Functor, Applicative, Monad, MonadIO, MonadUnliftIO, MonadLsp LSPConfig)

sendInfo :: T.Text -> LSPMonad ()
sendInfo msg = sendNotification SWindowShowMessage (ShowMessageParams MtInfo msg)

sendWarning :: T.Text -> LSPMonad ()
sendWarning msg = sendNotification SWindowShowMessage (ShowMessageParams MtWarning  msg)

sendError :: T.Text -> LSPMonad ()
sendError msg = sendNotification SWindowShowMessage (ShowMessageParams MtError msg)