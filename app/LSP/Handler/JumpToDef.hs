module LSP.Handler.JumpToDef ( jumpToDefHandler ) where

import Data.Map (Map)
import Data.Map qualified as M
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Language.LSP.Types
import Language.LSP.Server
import Language.LSP.VFS
import LSP.Definition
import LSP.MegaparsecToLSP
import System.Log.Logger
import Syntax.AST.Program
import Data.Maybe

import Driver.Definition
import Driver.Driver ( inferProgramIO )
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )

jumpToDefHandler :: Handlers LSPMonad
jumpToDefHandler = requestHandler STextDocumentDefinition $ \req responder -> do
    let (RequestMessage _ _ _ (DefinitionParams (TextDocumentIdentifier uri) pos _ _)) = req
    liftIO $ debugM "lspserver.JumpToDefHandler" ("Received definition request: " <> show uri <> " at: " <> show pos)
    mfile <- getVirtualFile (toNormalizedUri uri)
    let vfile :: VirtualFile = maybe (error "Virtual File not present!") id mfile
    let file = virtualFileText vfile
    let fp = fromMaybe "fail" (uriToFilePath uri)
    let decls = runFileParser fp programP file
    case decls of
      Left _err -> do
        responder (Left (ResponseError { _code = InvalidRequest, _message = "", _xdata = Nothing}))
      Right decls -> do
        res <- liftIO $ inferProgramIO defaultDriverState decls
        case res of
          Left _err -> do
            responder (Left (ResponseError { _code = InvalidRequest, _message = "", _xdata = Nothing}))
          Right (_,prog) -> do
            responder (generateJumpToDef pos prog)
    

generateJumpToDef :: Position -> Program -> Either ResponseError (Location |? b)
generateJumpToDef pos prog = do
    let jumpMap = toJumpMap prog
    case lookupInRangeMap pos jumpMap of
        Nothing -> (Left (ResponseError { _code = InvalidRequest, _message = "", _xdata = Nothing }))
        Just loc -> Right (InL loc)

class ToJumpMap a where
    toJumpMap :: a -> Map Range Location


instance ToJumpMap Program where
    toJumpMap _prog = M.empty