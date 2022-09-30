module LSP.Definition where

import Control.Monad.IO.Class ( MonadIO)
import Control.Monad.IO.Unlift (MonadUnliftIO)

import Data.Map (Map)
import Data.IORef
import Language.LSP.Server
import Language.LSP.Types
import Data.Text qualified as T
import qualified Data.List.NonEmpty as NE
import Errors (Error)
import Syntax.CST.Names (ModuleName(..))
import Control.Monad.Except (runExcept)
import Parser.Definition (runFileParser)
import Parser.Parser (moduleP)
import qualified Syntax.CST.Program as CST
---------------------------------------------------------------------------------
-- LSPMonad and Utility Functions
---------------------------------------------------------------------------------

type HoverMap   = Map Range Hover
type HoverCache = Map Uri HoverMap
newtype LSPConfig = MkLSPConfig (IORef HoverCache)

newtype LSPMonad a = MkLSPMonad { unLSPMonad :: LspT LSPConfig IO a }
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadUnliftIO, MonadLsp LSPConfig)

sendInfo :: T.Text -> LSPMonad ()
sendInfo msg = sendNotification SWindowShowMessage (ShowMessageParams MtInfo msg)

sendWarning :: T.Text -> LSPMonad ()
sendWarning msg = sendNotification SWindowShowMessage (ShowMessageParams MtWarning  msg)

sendError :: T.Text -> LSPMonad ()
sendError msg = sendNotification SWindowShowMessage (ShowMessageParams MtError msg)

getModuleFromFilePath :: FilePath -> T.Text -> Either (NE.NonEmpty Error) CST.Module
getModuleFromFilePath fp file = 
      let mn = MkModuleName [] "TODO"
      in  runExcept (runFileParser fp (moduleP fp mn) file)

