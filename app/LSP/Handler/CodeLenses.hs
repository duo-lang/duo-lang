module LSP.Handler.CodeLenses ( codeLensesHandler ) where

import Language.LSP.Server
import LSP.Definition
import Language.LSP.Types
import Language.LSP.VFS ( VirtualFile, virtualFileText )
import Data.Maybe ( fromMaybe )
import Parser.Definition ( runFileParser )
import Parser.Program ( moduleP )
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import System.Log.Logger (debugM)
import Driver.Definition
import Driver.Driver
import Syntax.TST.Program
import LSP.MegaparsecToLSP 
import Pretty.Pretty

---------------------------------------------------------------------------------
-- The code lens handler
---------------------------------------------------------------------------------

codeLensesHandler :: Handlers LSPMonad
codeLensesHandler = requestHandler STextDocumentCodeLens $ \req responder -> do
  let (RequestMessage _ _ _ (CodeLensParams _workDoneToken _partialResultToken (TextDocumentIdentifier uri))) = req
  liftIO $ debugM "lspserver.codeLensHandler" ("Received codeLens request: " <> show uri)
  mfile <- getVirtualFile (toNormalizedUri uri)
  let vfile :: VirtualFile = fromMaybe (error "Virtual File not present!") mfile
  let file = virtualFileText vfile
  let fp = fromMaybe "fail" (uriToFilePath uri)
  let decls = runFileParser fp (moduleP fp) file
  case decls of
    Left _err -> do
      responder (Right (List []))
    Right decls -> do
      (res,_warnings) <- liftIO $ inferProgramIO defaultDriverState decls
      case res of
        Left _err -> do
          responder (Right (List []))
        Right (_,prog) -> do
          responder (Right (toCodeLenses prog))

---------------------------------------------------------------------------------
-- Compute available code lenses
---------------------------------------------------------------------------------

class ToCodeLenses a where
    toCodeLenses :: a -> List CodeLens

instance ToCodeLenses Module where
    toCodeLenses :: Module -> List CodeLens
    toCodeLenses MkModule { mod_decls } = foldMap toCodeLenses mod_decls

instance ToCodeLenses Declaration where
    toCodeLenses :: Declaration -> List CodeLens
    toCodeLenses (PrdCnsDecl _ decl) = toCodeLenses decl
    toCodeLenses (CmdDecl decl) = toCodeLenses decl
    toCodeLenses (DataDecl decl) = toCodeLenses decl
    toCodeLenses (XtorDecl _) = mempty
    toCodeLenses (ImportDecl _) = mempty
    toCodeLenses (SetDecl _) = mempty
    toCodeLenses (TyOpDecl _) = mempty
    toCodeLenses (TySynDecl _) = mempty
    toCodeLenses (ClassDecl _) = mempty
    toCodeLenses (InstanceDecl _) = mempty

instance ToCodeLenses (PrdCnsDeclaration pol) where
    toCodeLenses :: PrdCnsDeclaration pol -> List CodeLens
    toCodeLenses = mempty

instance ToCodeLenses CommandDeclaration where
    toCodeLenses :: CommandDeclaration -> List CodeLens
    toCodeLenses = mempty

instance ToCodeLenses DataDecl where
    toCodeLenses :: DataDecl -> List CodeLens
    toCodeLenses (NominalDecl loc _doc nm _dc _knd _xtors) = do
      let cmd = Command { _title = "Dualize " <> ppPrint nm
                        , _command = "dualize-data-decl"
                        , _arguments = Nothing 
                        }
      let lens = CodeLens { _range = locToStartRange loc
                          , _command = Just cmd
                          , _xdata = Nothing
                          }
      List [lens]
    toCodeLenses RefinementDecl {} = mempty