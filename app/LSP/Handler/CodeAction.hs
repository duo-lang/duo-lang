{-# LANGUAGE TypeOperators #-}
module LSP.Handler.CodeAction (codeActionHandler) where

import Language.LSP.Types
import Language.LSP.Server
import Language.LSP.VFS
import Control.Monad (join)
import Data.Maybe ( fromMaybe, isNothing )
import System.Log.Logger ( debugM )
import Data.HashMap.Strict qualified as Map
import Control.Monad.IO.Class ( MonadIO(liftIO) )

import LSP.Definition ( LSPMonad )
import LSP.MegaparsecToLSP ( locToRange, lookupPos )
import Syntax.RST.Types ( TypeScheme, TopAnnot(..) )
import Syntax.Common
import Syntax.AST.Terms qualified as AST
import Syntax.AST.Program qualified as AST
import Syntax.Core.Program qualified as Core
import Driver.Definition
import Driver.Driver ( inferProgramIO )
import Utils
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint )
import Pretty.Program ()
import Translate.Focusing ( focusTerm, isFocusedTerm, isFocusedCmd, focusCmd )
import Translate.Desugar (desugarTerm, desugarCmd, isDesugaredTerm, isDesugaredCommand)

---------------------------------------------------------------------------------
-- Provide CodeActions
---------------------------------------------------------------------------------

codeActionHandler :: Handlers LSPMonad
codeActionHandler = requestHandler STextDocumentCodeAction $ \req responder -> do
  let (RequestMessage _ _ _ (CodeActionParams _workDoneToken _partialResultToken ident@(TextDocumentIdentifier uri) range _context)) = req
  liftIO $ debugM "lspserver.codeActionHandler" ("Received codeAction request: " <> show uri <> " range: " <> show range)
  mfile <- getVirtualFile (toNormalizedUri uri)
  let vfile :: VirtualFile = maybe (error "Virtual File not present!") id mfile
  let file = virtualFileText vfile
  let fp = fromMaybe "fail" (uriToFilePath uri)
  let decls = runFileParser fp programP file
  case decls of
    Left _err -> do
      responder (Right (List []))
    Right decls -> do
      res <- liftIO $ inferProgramIO defaultDriverState (MkModuleName (getUri uri)) decls
      case res of
        Left _err -> do
          responder (Right (List []))
        Right (_,prog) -> do
          responder (Right (generateCodeActions ident range prog))

generateCodeActions :: TextDocumentIdentifier -> Range -> AST.Program -> List (Command  |? CodeAction)
generateCodeActions ident rng program = List (join ls)
  where
    ls = generateCodeAction ident rng <$> program


generateCodeAction :: TextDocumentIdentifier -> Range -> AST.Declaration -> [Command |? CodeAction]
generateCodeAction ident (Range {_start = start }) (AST.PrdCnsDecl loc doc rep isrec fv (Inferred tys) tm) | lookupPos start loc =
  [generateAnnotCodeAction ident loc doc rep isrec fv tys tm]
generateCodeAction ident (Range {_start = start }) (AST.PrdCnsDecl loc _doc rep _isrec fv (Annotated tys) tm) = desugar ++ cbvfocus ++ cbnfocus
  where
    desugar  = [ generateDesugarCodeAction rep ident (fv, (tm, loc, tys)) | not (isDesugaredTerm tm), lookupPos start loc]
    cbvfocus = [ generateFocusCodeAction rep ident CBV (fv, (tm, loc, tys)) | isDesugaredTerm tm, isNothing (isFocusedTerm CBV (desugarTerm tm)), lookupPos start loc]
    cbnfocus = [ generateFocusCodeAction rep ident CBN (fv, (tm, loc, tys)) | isDesugaredTerm tm, isNothing (isFocusedTerm CBV (desugarTerm tm)), lookupPos start loc]
generateCodeAction ident (Range {_start = start}) (AST.CmdDecl loc _doc fv cmd) = desugar ++ cbvfocus ++ cbnfocus
  where
    desugar = [ generateCmdDesugarCodeAction ident (fv, (cmd, loc)) | not (isDesugaredCommand cmd), lookupPos start loc]
    cbvfocus = [ generateCmdFocusCodeAction ident CBN (fv, (cmd,loc)) | isDesugaredCommand cmd, isNothing (isFocusedCmd CBN (desugarCmd cmd)), lookupPos start loc]
    cbnfocus = [ generateCmdFocusCodeAction ident CBN (fv, (cmd,loc)) | isDesugaredCommand cmd, isNothing (isFocusedCmd CBN (desugarCmd cmd)), lookupPos start loc]
generateCodeAction _ _ _ = []

---------------------------------------------------------------------------------
-- Provide TypeAnnot Action
---------------------------------------------------------------------------------

generateAnnotCodeAction :: TextDocumentIdentifier -> Loc -> Maybe DocComment -> PrdCnsRep pc -> IsRec -> FreeVarName -> TypeScheme (PrdCnsToPol pc) -> AST.Term pc -> Command |? CodeAction
generateAnnotCodeAction (TextDocumentIdentifier uri) loc doc rep isrec fv tys tm = InR $ CodeAction { _title = "Annotate type for " <> ppPrint fv
                                                                             , _kind = Just CodeActionQuickFix
                                                                             , _diagnostics = Nothing
                                                                             , _isPreferred = Nothing
                                                                             , _disabled = Nothing
                                                                             , _edit = Just (generateAnnotEdit uri loc doc rep isrec fv tys tm) 
                                                                             , _command = Nothing
                                                                             , _xdata = Nothing
                                                                             }
generateAnnotEdit :: Uri -> Loc -> Maybe DocComment -> PrdCnsRep pc -> IsRec -> FreeVarName -> TypeScheme (PrdCnsToPol pc) -> AST.Term pc -> WorkspaceEdit
generateAnnotEdit uri loc doc rep isrec fv tys tm  =
  let
    newDecl :: AST.Declaration = AST.PrdCnsDecl loc doc rep isrec fv (Annotated tys) tm
    replacement = ppPrint newDecl
    edit = TextEdit {_range = locToRange loc, _newText = replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing }


---------------------------------------------------------------------------------
-- Provide Focus Actions
---------------------------------------------------------------------------------


generateFocusCodeAction :: PrdCnsRep pc -> TextDocumentIdentifier -> EvaluationOrder -> (FreeVarName, (AST.Term pc, Loc, TypeScheme (PrdCnsToPol pc))) -> Command |? CodeAction
generateFocusCodeAction rep ident eo arg@(name, _) = InR $ CodeAction { _title = "Focus " <> (case eo of CBV -> "CBV "; CBN -> "CBN ") <> unFreeVarName name
                                                                  , _kind = Just CodeActionQuickFix
                                                                  , _diagnostics = Nothing
                                                                  , _isPreferred = Nothing
                                                                  , _disabled = Nothing
                                                                  , _edit = Just (generateFocusEdit rep eo ident arg)
                                                                  , _command = Nothing
                                                                  , _xdata = Nothing
                                                                  }

generateFocusEdit :: PrdCnsRep pc -> EvaluationOrder -> TextDocumentIdentifier ->  (FreeVarName, (AST.Term pc, Loc, TypeScheme (PrdCnsToPol pc))) -> WorkspaceEdit
generateFocusEdit pc eo (TextDocumentIdentifier uri) (name,(tm,loc,ty)) =
  let
    newDecl :: Core.Declaration = case pc of
                PrdRep -> Core.PrdCnsDecl defaultLoc Nothing PrdRep Recursive name (Inferred ty) (focusTerm eo (desugarTerm tm))
                CnsRep -> Core.PrdCnsDecl defaultLoc Nothing CnsRep Recursive name (Inferred ty) (focusTerm eo (desugarTerm tm))
    replacement = ppPrint newDecl
    edit = TextEdit {_range= locToRange loc, _newText= replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }

generateCmdFocusCodeAction :: TextDocumentIdentifier -> EvaluationOrder -> (FreeVarName, (AST.Command, Loc)) -> Command |? CodeAction
generateCmdFocusCodeAction ident eo arg@(name, _) = InR $ CodeAction { _title = "Focus " <> (case eo of CBV -> "CBV "; CBN -> "CBN ") <> unFreeVarName name
                                                                  , _kind = Just CodeActionQuickFix
                                                                  , _diagnostics = Nothing
                                                                  , _isPreferred = Nothing
                                                                  , _disabled = Nothing
                                                                  , _edit = Just (generateCmdFocusEdit eo ident arg)
                                                                  , _command = Nothing
                                                                  , _xdata = Nothing
                                                                  }

generateCmdFocusEdit ::  EvaluationOrder -> TextDocumentIdentifier ->  (FreeVarName, (AST.Command, Loc)) -> WorkspaceEdit
generateCmdFocusEdit eo (TextDocumentIdentifier uri) (name,(cmd,loc)) =
  let
    newDecl = Core.CmdDecl defaultLoc Nothing name (focusCmd eo (desugarCmd cmd))
    replacement = ppPrint newDecl
    edit = TextEdit {_range= locToRange loc, _newText= replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }

---------------------------------------------------------------------------------
-- Provide Desugar Actions
---------------------------------------------------------------------------------

generateDesugarCodeAction :: PrdCnsRep pc -> TextDocumentIdentifier -> (FreeVarName,(AST.Term pc, Loc, TypeScheme (PrdCnsToPol pc))) -> Command |? CodeAction
generateDesugarCodeAction rep ident arg@(name,_) = InR $ CodeAction { _title = "Desugar " <> unFreeVarName name
                                                                    , _kind = Just CodeActionQuickFix
                                                                    , _diagnostics = Nothing
                                                                    , _isPreferred = Nothing
                                                                    , _disabled = Nothing
                                                                    , _edit = Just (generateDesugarEdit rep ident arg)
                                                                    , _command = Nothing
                                                                    , _xdata = Nothing
                                                                    }

generateDesugarEdit :: PrdCnsRep pc -> TextDocumentIdentifier  -> (FreeVarName,(AST.Term pc, Loc, TypeScheme (PrdCnsToPol pc))) -> WorkspaceEdit
generateDesugarEdit rep (TextDocumentIdentifier uri) (name, (tm,loc,ty)) =
  let
    newDecl = Core.PrdCnsDecl defaultLoc Nothing rep Recursive name (Inferred ty) (desugarTerm tm)
    replacement = ppPrint newDecl
    edit = TextEdit {_range=locToRange loc, _newText=replacement}
  in
    WorkspaceEdit { _changes= Just (Map.singleton uri (List [edit]))
                  , _documentChanges=Nothing
                  , _changeAnnotations=Nothing}

generateCmdDesugarCodeAction ::  TextDocumentIdentifier -> (FreeVarName, (AST.Command, Loc)) -> Command |? CodeAction
generateCmdDesugarCodeAction ident arg@(name,_) = InR $ CodeAction { _title = "Desugar " <> unFreeVarName name
                                                                   , _kind = Just CodeActionQuickFix
                                                                   , _diagnostics = Nothing
                                                                   , _isPreferred = Nothing
                                                                   , _disabled = Nothing
                                                                   , _edit = Just (generateCmdDesugarEdit ident arg)
                                                                   , _command = Nothing
                                                                   , _xdata = Nothing
                                                                   }

generateCmdDesugarEdit :: TextDocumentIdentifier -> (FreeVarName, (AST.Command, Loc)) -> WorkspaceEdit
generateCmdDesugarEdit (TextDocumentIdentifier uri) (name, (cmd,loc)) =
  let
    newDecl = Core.CmdDecl defaultLoc Nothing name (desugarCmd cmd)
    replacement = ppPrint newDecl
    edit = TextEdit {_range = locToRange loc, _newText= replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }