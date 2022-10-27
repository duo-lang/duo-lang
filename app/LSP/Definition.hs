module LSP.Definition where

import Control.Monad.Except (runExcept)
import Control.Monad.IO.Class ( MonadIO(..) )
import Control.Monad.IO.Unlift (MonadUnliftIO)
import Data.IORef ( IORef, modifyIORef', readIORef )
import Data.List.NonEmpty qualified as NE
import Data.Map ( Map )
import Data.Map qualified as M
import Data.Maybe ( fromMaybe )
import Data.SortedList qualified as SL
import Data.Text qualified as T
import Language.LSP.Server qualified as LSP
import Language.LSP.Types qualified as LSP
import Language.LSP.VFS ( virtualFileText )

import Driver.Definition ( defaultDriverState )
import Driver.Driver ( inferProgramIO )
import Errors ( Warning, Error )
import Loc ( getLoc )
import LSP.MegaparsecToLSP ( locToRange )
import Parser.Definition (runFileParser)
import Parser.Program ( moduleP )
import Pretty.Pretty ( ppPrint )
import Syntax.CST.Program qualified as CST
import Syntax.TST.Program qualified as TST

---------------------------------------------------------------------------------
-- LSPMonad and Utility Functions
---------------------------------------------------------------------------------


newtype LSPConfig = MkLSPConfig { tst_map :: IORef (Map LSP.Uri TST.Module) }

updateCache :: LSP.Uri -> TST.Module -> LSPMonad ()
updateCache uri mod = do
  MkLSPConfig ref <- LSP.getConfig
  liftIO $ modifyIORef' ref (M.insert uri mod)

getCachedModule :: LSP.Uri -> LSPMonad (Maybe TST.Module)
getCachedModule uri = do
  MkLSPConfig ref <- LSP.getConfig
  m <- liftIO $ readIORef ref
  pure $ M.lookup uri m

newtype LSPMonad a = MkLSPMonad { unLSPMonad :: LSP.LspT LSPConfig IO a }
  deriving newtype (Functor, Applicative, Monad, MonadIO, MonadUnliftIO, LSP.MonadLsp LSPConfig)

sendInfo :: T.Text -> LSPMonad ()
sendInfo msg = LSP.sendNotification LSP.SWindowShowMessage (LSP.ShowMessageParams LSP.MtInfo msg)

sendWarning :: T.Text -> LSPMonad ()
sendWarning msg = LSP.sendNotification LSP.SWindowShowMessage (LSP.ShowMessageParams LSP.MtWarning  msg)

sendError :: T.Text -> LSPMonad ()
sendError msg = LSP.sendNotification LSP.SWindowShowMessage (LSP.ShowMessageParams LSP.MtError msg)

getModuleFromFilePath :: FilePath -> T.Text -> Either (NE.NonEmpty Error) CST.Module
getModuleFromFilePath fp file = do
  mod <- runExcept (runFileParser fp (moduleP fp) file)
  CST.adjustModulePath mod fp

---------------------------------------------------------------------------------------------
-- Publishing Diagnostics
---------------------------------------------------------------------------------------------

class IsDiagnostic a where
  toDiagnostic :: a -> [LSP.Diagnostic]

instance IsDiagnostic Warning where
  toDiagnostic :: Warning -> [LSP.Diagnostic]
  toDiagnostic warn = [diag]
    where
      diag = LSP.Diagnostic { _range = locToRange (getLoc warn)
                            , _severity = Just LSP.DsWarning
                            , _code = Nothing
                            , _source = Nothing
                            , _message = ppPrint warn
                            , _tags = Nothing
                            , _relatedInformation = Nothing
                            }

instance IsDiagnostic Error where
  toDiagnostic :: Error -> [LSP.Diagnostic]
  toDiagnostic err = [diag]
    where
      diag = LSP.Diagnostic { _range = locToRange (getLoc err)
                            , _severity = Just LSP.DsError
                            , _code = Nothing
                            , _source = Nothing
                            , _message = ppPrint err
                            , _tags = Nothing
                            , _relatedInformation = Nothing
                            }

sendDiagnostics :: IsDiagnostic a => LSP.NormalizedUri -> [a] -> LSPMonad ()
sendDiagnostics uri w = do
  let diags = concatMap toDiagnostic w
  LSP.publishDiagnostics 42 uri Nothing (M.fromList [(Just "Duo", SL.toSortedList diags)])

---------------------------------------------------------------------------------------------
-- Main loop
---------------------------------------------------------------------------------------------

publishErrors :: LSP.Uri -> LSPMonad ()
publishErrors uri = do
  LSP.flushDiagnosticsBySource 42 (Just "TypeInference")
  mfile <- LSP.getVirtualFile (LSP.toNormalizedUri uri)
  case mfile of
    Nothing -> sendError "Virtual File not present!"
    Just vfile -> do
      let file = virtualFileText vfile
      let fp = fromMaybe "fail" (LSP.uriToFilePath uri)
      let decls = getModuleFromFilePath fp file
      case decls of
        Left errs -> do
          sendDiagnostics (LSP.toNormalizedUri uri) (NE.toList errs)
        Right decls -> do
          (res, warnings) <- liftIO $ inferProgramIO defaultDriverState decls
          sendDiagnostics (LSP.toNormalizedUri uri) warnings
          case res of
            Left errs -> do
              sendDiagnostics (LSP.toNormalizedUri uri) (NE.toList errs)
            Right (_,mod) -> do
              updateCache uri mod
