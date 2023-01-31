module LSP.Handler.CodeAction (codeActionHandler
                              , evalHandler
                              ) where

import GHC.Generics ( Generic )
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.HashMap.Strict qualified as Map
import Data.Maybe ( fromMaybe, isNothing )
import Data.Text (Text)
import Data.Text qualified as T
import Language.LSP.Types ( TextDocumentIdentifier(..)
                          , RequestMessage (..)
                          , CodeActionParams (..)
                          , Range (..)
                          , List (..)
                          , Command (..)
                          , type (|?) (..)
                          , CodeAction (..)
                          , Uri
                          , WorkspaceEdit (..)
                          , TextEdit (..)
                          , ResponseError (..)
                          , ExecuteCommandParams (..)
                          , ApplyWorkspaceEditParams (..)
                          , SMethod (..)
                          , uriToFilePath
                          , CodeActionKind (..)
                          , ErrorCode (..))
import Language.LSP.Server
    (  requestHandler, sendRequest, Handlers, getConfig )
import System.Log.Logger ( debugM )
import Syntax.TST.Types qualified as TST ( TopAnnot(..))
import Syntax.CST.Kinds ( EvaluationOrder(..) )
import Syntax.TST.Program qualified as TST
import Syntax.CST.Types (PrdCnsRep(..))
import Driver.Definition
    ( DriverState(MkDriverState, drvEnv),
      defaultDriverState,
      execDriverM,
      queryTypecheckedModule )
import Driver.Driver ( runCompilationModule )
import Dualize.Dualize (dualDataDecl, dualPrdCnsDeclaration, dualCmdDeclaration)
import Xfunctionalize.Xfunctionalize qualified as XFunc
import LSP.Definition ( LSPMonad, LSPConfig (..), sendInfo, getCachedModule )
import LSP.MegaparsecToLSP ( locToRange, lookupPos, locToEndRange )
import Pretty.Pretty ( ppPrint )
import Pretty.Program ()
import Sugar.TST (isDesugaredTerm, isDesugaredCommand, resetAnnotationTerm, resetAnnotationCmd)
import Syntax.CST.Names ( FreeVarName(..), ModuleName )
import Translate.Focusing ( Focus(..) )
import Loc ( Loc, defaultLoc )
import Eval.Eval (eval, EvalMWrapper (..))
import qualified Syntax.TST.Terms as TST
import Data.List.NonEmpty (NonEmpty ((:|)))
import Control.Monad.State.Strict (execStateT)
import Control.Monad.Writer.Strict (execWriter)
import qualified Data.Aeson as J
import Eval.Definition (EvalEnv)
import Data.Foldable (fold)
import Run (desugarEnv)
import qualified Data.Map as M
import Utils (filePathToModuleName)
import System.Directory (makeRelativeToCurrentDirectory)
import Data.IORef (readIORef)


---------------------------------------------------------------------------------
-- Provide CodeActions
---------------------------------------------------------------------------------

codeActionHandler :: Handlers LSPMonad
codeActionHandler = requestHandler STextDocumentCodeAction $ \req responder -> do
  let (RequestMessage _ _ _ (CodeActionParams _workDoneToken _partialResultToken ident@(TextDocumentIdentifier uri) range _context)) = req
  liftIO $ debugM "lspserver.codeActionHandler" ("Received codeAction request: " <> show uri <> " range: " <> show range)
  MkLSPConfig ref <- getConfig
  cache <- liftIO $ readIORef ref
  case M.lookup uri cache of
    Nothing -> do
      sendInfo ("Cache not initialized for: " <> T.pack (show uri))
      responder (Right (List []))
    Just mod -> responder (Right (getCodeActions ident range mod))
      




  -- mfile <- getVirtualFile (toNormalizedUri uri)
  -- let vfile :: VirtualFile = fromMaybe (error "Virtual File not present!") mfile
  -- let file = virtualFileText vfile
  -- let fp = fromMaybe "fail" (uriToFilePath uri)
  -- let decls = getModuleFromFilePath  fp file
  -- case decls of
  --   Left _err -> do
  --     responder (Right (List []))
  --   Right decls -> do
  --     (res,_warnings) <- liftIO $ inferProgramIO defaultDriverState decls
  --     case res of
  --       Left _err -> do
  --         responder (Right (List []))
  --       Right (_,prog) -> do
  --         


workspaceEditToCodeAction :: WorkspaceEdit -> Text -> Command |? CodeAction
workspaceEditToCodeAction edit descr =
  InR $ CodeAction { _title = descr
                   , _kind = Just CodeActionQuickFix
                   , _diagnostics = Nothing
                   , _isPreferred = Nothing
                   , _disabled = Nothing
                   , _edit = Just edit
                   , _command = Nothing
                   , _xdata = Nothing
                   }


workspaceEditToCodeActionWithCommand :: (WorkspaceEdit |? WorkspaceEdit) -> Text -> Command |? CodeAction
workspaceEditToCodeActionWithCommand (InR edit) descr =
  InR $ CodeAction { _title = descr
                   , _kind = Just CodeActionQuickFix
                   , _diagnostics = Nothing
                   , _isPreferred = Nothing
                   , _disabled = Nothing
                   , _edit = Just edit
                   , _command = Nothing
                   , _xdata = Nothing
                   }
workspaceEditToCodeActionWithCommand (InL _) descr =
  InR $ CodeAction { _title = descr
                   , _kind = Just CodeActionQuickFix
                   , _diagnostics = Nothing
                   , _isPreferred = Nothing
                   , _disabled = Nothing
                   , _edit = Nothing
                   , _command = Just (Command{_title="transformation_not_possible", _command="transformation-not-possible" , _arguments=Nothing})
                   , _xdata = Nothing
                   }


---------------------------------------------------------------------------------
-- Class for generating code actions
---------------------------------------------------------------------------------

class GetCodeActions a where
  getCodeActions :: TextDocumentIdentifier
                 -- ^ The document in which we are looking for available Code actions.
                 -> Range
                 -- ^ The range where we are looking for available code actions, i.e.
                 --   the position of the mouse pointer.
                 -> a 
                 -- ^ The element in which we are searching for available code actions.
                 -> List (Command |? CodeAction)
                 -- ^ The available code actions and commands.

instance GetCodeActions TST.Module where
  getCodeActions :: TextDocumentIdentifier -> Range -> TST.Module -> List (Command |? CodeAction)
  getCodeActions id rng TST.MkModule { mod_decls } = mconcat (getCodeActions id rng <$> mod_decls)
  
instance GetCodeActions TST.Declaration where
  getCodeActions :: TextDocumentIdentifier -> Range -> TST.Declaration -> List (Command |? CodeAction)
  getCodeActions id rng (TST.PrdCnsDecl _ decl)  = getCodeActions id rng decl
  getCodeActions id rng (TST.CmdDecl decl)       = getCodeActions id rng decl
  getCodeActions id rng (TST.DataDecl decl)      = getCodeActions id rng decl
  getCodeActions _ _ _                           = List []


--Code actions for producer and consumer definitions
instance GetCodeActions (TST.PrdCnsDeclaration pc) where
  getCodeActions :: TextDocumentIdentifier -> Range -> TST.PrdCnsDeclaration pc -> List (Command |? CodeAction)
  -- If we are not in the correct range, then don't generate code actions.
  getCodeActions _ Range { _start = start } decl | not (lookupPos start (TST.pcdecl_loc decl)) =
    List []
  -- If the type is not already annotated, only generate the code action for annotating the type.
  getCodeActions id _ decl@TST.MkPrdCnsDeclaration { pcdecl_annot = TST.Inferred _ } =
    List [workspaceEditToCodeAction (generateAnnotEdit id decl) ("Annotate type for " <> ppPrint (TST.pcdecl_name decl))]
  -- If the type is annotated, generate the remaining code actions.
  getCodeActions id _ decl@TST.MkPrdCnsDeclaration { pcdecl_annot = TST.Annotated _, pcdecl_term } =
    let
      desugar  = [ workspaceEditToCodeAction (generateDesugarEdit id decl) ("Desugar " <> unFreeVarName (TST.pcdecl_name decl)) | not (isDesugaredTerm pcdecl_term)]
      cbvfocus = [ workspaceEditToCodeAction (generateFocusEdit id CBV decl) ("Focus CBV " <> unFreeVarName (TST.pcdecl_name decl)) | isDesugaredTerm pcdecl_term, isNothing (isFocused CBV pcdecl_term)]
      cbnfocus = [ workspaceEditToCodeAction (generateFocusEdit id CBN decl) ("Focus CBN " <> unFreeVarName (TST.pcdecl_name decl)) | isDesugaredTerm pcdecl_term, isNothing (isFocused CBN pcdecl_term)]
      dualize  = [ workspaceEditToCodeAction (generateDualizeEdit id decl) ("Dualize term " <> ppPrint (TST.pcdecl_name decl)) ]
    in
      List (desugar <> cbvfocus <> cbnfocus <> dualize)

-- code actions for command declerations
instance GetCodeActions TST.CommandDeclaration where
  getCodeActions :: TextDocumentIdentifier -> Range -> TST.CommandDeclaration -> List (Command |? CodeAction)
  -- If we are not in the correct range, then don't generate code actions.
  getCodeActions _ Range { _start = start } decl | not (lookupPos start (TST.cmddecl_loc decl)) =
    List []
  getCodeActions id _ decl@TST.MkCommandDeclaration {cmddecl_cmd } =
    let
      desugar  = [ workspaceEditToCodeAction (generateCmdDesugarEdit id decl) ("Desugar " <> unFreeVarName (TST.cmddecl_name decl)) | not (isDesugaredCommand cmddecl_cmd)]
      cbvfocus = [ workspaceEditToCodeAction (generateCmdFocusEdit id CBV decl) ("Focus CBV " <> unFreeVarName (TST.cmddecl_name decl)) | isDesugaredCommand cmddecl_cmd, isNothing (isFocused CBV cmddecl_cmd)]
      cbnfocus = [ workspaceEditToCodeAction (generateCmdFocusEdit id CBN decl) ("Focus CBN " <> unFreeVarName (TST.cmddecl_name decl)) | isDesugaredCommand cmddecl_cmd, isNothing (isFocused CBN cmddecl_cmd)]
      eval     = [ generateCmdEvalCodeAction id decl ]
      dualize  = [ workspaceEditToCodeAction (generateDualizeCommandEdit id decl) ("Dualize command " <> ppPrint (TST.cmddecl_name decl)) ]
    in
      List (desugar <> cbvfocus <> cbnfocus <> dualize <> eval)

-- code actions for data declarations 
instance GetCodeActions TST.DataDecl where
  getCodeActions :: TextDocumentIdentifier -> Range -> TST.DataDecl -> List (Command |? CodeAction)
  -- If we are not in the correct range, then don't generate code actions.
  getCodeActions _ Range {_start = start} decl | not (lookupPos start (TST.data_loc decl)) =
    List []
  getCodeActions id _ decl =
    let
      dualize = [ workspaceEditToCodeAction (generateDualizeDeclEdit id (TST.data_loc decl) decl) ("Dualize declaration " <> ppPrint (TST.data_name decl)) ]
      xfunctionalize = [ workspaceEditToCodeActionWithCommand (generateXfunctionalizeDeclEdit id (TST.data_loc decl) decl) ("Xfunctionalize declaration" <> ppPrint (TST.data_name decl))]
    in
      List (dualize <> xfunctionalize)

---------------------------------------------------------------------------------
-- Provide TypeAnnot Action
---------------------------------------------------------------------------------


generateAnnotEdit :: forall pc. TextDocumentIdentifier -> TST.PrdCnsDeclaration pc -> WorkspaceEdit
generateAnnotEdit (TextDocumentIdentifier uri) (TST.MkPrdCnsDeclaration loc doc rep isrec fv (TST.Inferred tys) tm) =
  let
    newDecl :: TST.Declaration
    newDecl = TST.PrdCnsDecl rep (TST.MkPrdCnsDeclaration loc doc rep isrec fv (TST.Annotated tys) tm)
    replacement = ppPrint newDecl
    edit = TextEdit {_range = locToRange loc, _newText = replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing }
generateAnnotEdit _ TST.MkPrdCnsDeclaration { pcdecl_annot = TST.Annotated _ } = error "Should not occur"

---------------------------------------------------------------------------------
-- Provide Dualize Action
---------------------------------------------------------------------------------

generateDualizeCommandEdit :: TextDocumentIdentifier -> TST.CommandDeclaration -> WorkspaceEdit
generateDualizeCommandEdit (TextDocumentIdentifier uri) decl@(TST.MkCommandDeclaration loc _ _ _) =
  let
    replacement = case dualCmdDeclaration decl of
      (Left error) -> ppPrint $ T.pack (show error)
      (Right decl') -> ppPrint (TST.CmdDecl decl')
    edit = TextEdit {_range = locToEndRange loc, _newText = T.pack "\n" `T.append` replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing }


generateDualizeEdit :: forall pc. TextDocumentIdentifier -> TST.PrdCnsDeclaration pc -> WorkspaceEdit
generateDualizeEdit (TextDocumentIdentifier uri) decl@(TST.MkPrdCnsDeclaration loc _ rep _ _ _ _) =
  let
    replacement = case dualPrdCnsDeclaration decl of
      (Left error) -> ppPrint $ T.pack (show error)
      (Right decl') -> case rep of
        PrdRep -> ppPrint (TST.PrdCnsDecl CnsRep decl')
        CnsRep -> ppPrint (TST.PrdCnsDecl PrdRep decl')
    edit = TextEdit {_range = locToEndRange loc, _newText = T.pack "\n" `T.append` replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing }


generateDualizeDeclEdit :: TextDocumentIdentifier -> Loc -> TST.DataDecl -> WorkspaceEdit
generateDualizeDeclEdit (TextDocumentIdentifier uri) loc decl =
  let
    decl' = dualDataDecl decl
    replacement = ppPrint (TST.DataDecl  decl')
    edit = TextEdit {_range = locToEndRange loc, _newText = T.pack "\n" `T.append` replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing }


---------------------------------------------------------------------------------
-- Provide De- and Refunctianlization Action
-- no implementation yet
---------------------------------------------------------------------------------
generateXfunctionalizeDeclEdit :: TextDocumentIdentifier -> Loc -> TST.DataDecl -> (WorkspaceEdit |? WorkspaceEdit)
generateXfunctionalizeDeclEdit (TextDocumentIdentifier uri) loc decl = 
  let 
    transformable = XFunc.transformable decl
  in
    if transformable then
      InR $ WorkspaceEdit{ _changes = Nothing
                         , _documentChanges = Nothing
                         , _changeAnnotations = Nothing};
    else
      InL $ WorkspaceEdit{ _changes = Nothing
                         , _documentChanges = Nothing
                         , _changeAnnotations = Nothing};


---------------------------------------------------------------------------------
-- Provide Focus Actions
---------------------------------------------------------------------------------

generateFocusEdit :: forall pc.TextDocumentIdentifier -> EvaluationOrder -> TST.PrdCnsDeclaration pc -> WorkspaceEdit
generateFocusEdit (TextDocumentIdentifier uri) eo decl =
  let
    newDecl :: TST.Declaration
    newDecl = TST.PrdCnsDecl (TST.pcdecl_pc decl) (focus eo decl)
    replacement = ppPrint newDecl
    edit = TextEdit {_range = locToRange (TST.pcdecl_loc decl), _newText = replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }

generateCmdFocusEdit :: TextDocumentIdentifier -> EvaluationOrder -> TST.CommandDeclaration -> WorkspaceEdit
generateCmdFocusEdit (TextDocumentIdentifier uri) eo decl =
  let
    newDecl = TST.CmdDecl (focus eo decl)
    replacement = ppPrint newDecl
    edit = TextEdit {_range= locToRange (TST.cmddecl_loc decl), _newText= replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }

---------------------------------------------------------------------------------
-- Provide Desugar Actions
---------------------------------------------------------------------------------

generateDesugarEdit :: forall pc. TextDocumentIdentifier  -> TST.PrdCnsDeclaration pc -> WorkspaceEdit
generateDesugarEdit (TextDocumentIdentifier uri) (TST.MkPrdCnsDeclaration loc doc rep isRec name (TST.Annotated ty) tm) =
  let
    newDecl = TST.PrdCnsDecl rep (TST.MkPrdCnsDeclaration defaultLoc doc rep isRec name (TST.Annotated ty) (resetAnnotationTerm tm))
    replacement = ppPrint newDecl
    edit = TextEdit {_range =locToRange loc, _newText = replacement}
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing}
generateDesugarEdit _ TST.MkPrdCnsDeclaration { pcdecl_annot = TST.Inferred _ } = error "Should not occur"

generateCmdDesugarEdit :: TextDocumentIdentifier -> TST.CommandDeclaration -> WorkspaceEdit
generateCmdDesugarEdit (TextDocumentIdentifier uri) decl =
  let
    newDecl = TST.CmdDecl (TST.MkCommandDeclaration defaultLoc Nothing (TST.cmddecl_name decl) (resetAnnotationCmd (TST.cmddecl_cmd decl)))
    replacement = ppPrint newDecl
    edit = TextEdit {_range = locToRange (TST.cmddecl_loc decl), _newText = replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }

data EvalCmdArgs = MkEvalCmdArgs  { evalArgs_loc :: Range
                                  , evalArgs_uri :: TextDocumentIdentifier
                                  , evalArgs_cmd :: FreeVarName
                                  }
  deriving (Show, Generic)

deriving anyclass instance J.FromJSON EvalCmdArgs
deriving anyclass instance J.ToJSON EvalCmdArgs

generateCmdEvalCodeAction ::  TextDocumentIdentifier -> TST.CommandDeclaration -> Command |? CodeAction
generateCmdEvalCodeAction ident decl =
  let cmd = TST.cmddecl_name decl
      args = MkEvalCmdArgs  { evalArgs_loc = locToRange (TST.cmddecl_loc decl)
                            , evalArgs_uri = ident
                            , evalArgs_cmd = cmd
                            }
  in InR $ CodeAction { _title = "Eval " <> unFreeVarName (TST.cmddecl_name decl)
                      , _kind = Just CodeActionQuickFix
                      , _diagnostics = Nothing
                      , _isPreferred = Nothing
                      , _disabled = Nothing
                      --  , _edit = Just (generateCmdEvalEdit ident decl)
                      , _edit = Nothing
                      , _command = Just $ Command { _title = "eval", _command = "duo-inline-eval", _arguments = Just $ List [J.toJSON args] }
                      , _xdata = Nothing
                      }

stopHandler :: (Either ResponseError b -> LSPMonad ()) -> String -> String -> LSPMonad a
stopHandler responder s e = responder (Left $ ResponseError InvalidRequest (T.pack e) Nothing) >> liftIO (debugM s e >> fail e)

uriToModuleName :: Uri -> LSPMonad ModuleName
uriToModuleName uri = do
      let fullPath = fromMaybe "" $ uriToFilePath uri
      relPath <- liftIO $ makeRelativeToCurrentDirectory fullPath
      return $ filePathToModuleName relPath

evalArgsFromJSON  :: LSPMonad EvalCmdArgs
                  -> LSPMonad EvalCmdArgs
                  -> (String -> LSPMonad EvalCmdArgs)
                  -> Maybe (List J.Value)
                  -> LSPMonad EvalCmdArgs
evalArgsFromJSON emptyFail tooManyFail errFail = maybe emptyFail getJSON
  where
    getJSON :: List J.Value -> LSPMonad EvalCmdArgs
    getJSON (List xs) = case xs of
                          [] -> emptyFail
                          [args] -> case J.fromJSON args :: J.Result EvalCmdArgs of
                                      J.Success ea -> return ea
                                      J.Error e    -> do
                                          errFail e
                          _xs -> tooManyFail

evalInModule  :: MonadIO m
              => ModuleName
              -> FreeVarName
              -> (String -> m (TST.Module, DriverState))
              -> m [String]
evalInModule mn cmd stop = do
      (res, _warnings) <- liftIO $ execDriverM defaultDriverState (runCompilationModule mn >> queryTypecheckedModule mn)
      (_, MkDriverState { drvEnv }) <- case res of
                  Left errs -> stop $ unlines $ (\(x :| xs) -> x:xs) $ show <$> errs
                  Right drvEnv -> return drvEnv
      let compiledEnv :: EvalEnv = focus CBV ((\map -> fold $ desugarEnv <$> M.elems map) drvEnv)
      return $ execWriter $ flip execStateT [] $ unEvalMWrapper $ eval (TST.Jump defaultLoc cmd) compiledEnv

addCommentedAbove :: Foldable t => Range -> Uri -> t String -> ApplyWorkspaceEditParams
addCommentedAbove range uri content =
      let toComments = unlines . fmap ("-- " ++) . concatMap lines
          rangeToStartRange Range { _start } = Range {_start = _start, _end = _start}
          tedit = TextEdit { _range = rangeToStartRange range, _newText = T.pack $ toComments content}
          wedit = WorkspaceEdit { _changes = Just (Map.singleton uri (List [tedit]))
                                , _documentChanges = Nothing
                                , _changeAnnotations = Nothing
                                }
      in  ApplyWorkspaceEditParams { _label = Nothing, _edit = wedit }

evalHandler :: Handlers LSPMonad
evalHandler = requestHandler SWorkspaceExecuteCommand $ \RequestMessage{_params} responder -> do
  let source = "lspserver.evalHandler"
  let ExecuteCommandParams{_command, _arguments} = _params
  case _command of
    "duo-inline-eval" -> do
      -- parse arguments back from JSON
      liftIO $ debugM source "Received eval request"
      args <- evalArgsFromJSON
                (stopHandler responder source "Arguments should not be empty")
                (stopHandler responder source "Specified more than one argument!")
                (\e -> stopHandler responder source ("Request " <> T.unpack _command <> " is invalid with error " <> e))
                _arguments
      liftIO $ debugM source $ "Running " <> T.unpack _command <> " with args " <> show args


      -- get Module name
      let uri = _uri $ evalArgs_uri args
      mmod <- getCachedModule uri

      mn <- case mmod of
              Nothing  -> uriToModuleName uri
              Just mod -> pure $ TST.mod_name mod
      liftIO $ debugM source $ "Running " <> T.unpack _command <> " with module " <> show mn

      -- execute command
      res <- evalInModule mn (evalArgs_cmd args) (stopHandler responder source)
      liftIO $ debugM source $ "Running " <> T.unpack _command <> " with result " <> unlines res

      -- create edit
      let weditP = addCommentedAbove (evalArgs_loc args) uri res
      let responder' x = case x of
                          Left e  -> responder (Left e)
                          Right _ -> return ()
      _ <- sendRequest SWorkspaceApplyEdit weditP responder'

      -- signal success
      responder (Right $ J.toJSON ())
    "transformation-not-possible" -> do
      liftIO $ debugM source "Received transformation request"
      sendInfo "Transformation not possible"
    _ -> responder (Left $ ResponseError InvalidRequest ("Request " <> _command <> " is invalid") Nothing)

