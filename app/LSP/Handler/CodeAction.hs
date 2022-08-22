{-# LANGUAGE TypeOperators #-}
module LSP.Handler.CodeAction (codeActionHandler) where

import Language.LSP.Types
import Language.LSP.Server
import Language.LSP.VFS
import Control.Monad (join)
import Data.Maybe ( fromMaybe, isNothing )
import System.Log.Logger ( debugM )
import Data.HashMap.Strict qualified as Map
import Data.Text qualified as T
import Control.Monad.IO.Class ( MonadIO(liftIO) )

import LSP.Definition ( LSPMonad )
import LSP.MegaparsecToLSP ( locToRange, lookupPos, locToEndRange )
import Syntax.RST.Types ( TopAnnot(..))
import Syntax.CST.Kinds ( EvaluationOrder(..) )
import Syntax.Common.Names ( FreeVarName(unFreeVarName) )
import Syntax.Common.PrdCns ( PrdCnsRep(..) )
import Syntax.TST.Program qualified as TST
import Syntax.RST.Program qualified as RST
import Driver.Definition
import Driver.Driver ( inferProgramIO )
import Utils
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint )
import Pretty.Program ()
import Translate.Focusing ( isFocusedTerm, isFocusedCmd, focusPrdCnsDeclaration, focusCommandDeclaration)
import Sugar.TST (isDesugaredTerm, isDesugaredCommand, resetAnnotationTerm, resetAnnotationCmd)
import Dualize.Terms (dualTerm, dualTypeScheme, dualFVName)
import Syntax.Common.Polarity
import Data.Text (pack, append)
import Dualize.Program (dualDataDecl)

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
      (res,_warnings) <- liftIO $ inferProgramIO defaultDriverState (T.unpack (getUri uri)) decls
      case res of
        Left _err -> do
          responder (Right (List []))
        Right (_,prog) -> do
          responder (Right (generateCodeActions ident range prog))

generateCodeActions :: TextDocumentIdentifier -> Range -> TST.Program -> List (Command  |? CodeAction)
generateCodeActions ident rng program = List (join ls)
  where
    ls = generateCodeAction ident rng <$> program


generateCodeActionPrdCnsDeclaration :: TextDocumentIdentifier -> TST.PrdCnsDeclaration pc -> [Command |? CodeAction]
generateCodeActionPrdCnsDeclaration ident decl@TST.MkPrdCnsDeclaration { pcdecl_annot = Inferred _ } =
  [generateAnnotCodeAction ident decl]
generateCodeActionPrdCnsDeclaration ident decl@TST.MkPrdCnsDeclaration { pcdecl_annot = Annotated _, pcdecl_term } =
  let
    desugar  = [ generateDesugarCodeAction ident decl | not (isDesugaredTerm pcdecl_term)]
    cbvfocus = [ generateFocusCodeAction ident CBV decl | isDesugaredTerm pcdecl_term, isNothing (isFocusedTerm CBV pcdecl_term)]
    cbnfocus = [ generateFocusCodeAction ident CBN decl | isDesugaredTerm pcdecl_term, isNothing (isFocusedTerm CBN pcdecl_term)]
    dualize  = [ generateDualizeCodeAction ident decl]
  in
    desugar ++ cbvfocus ++ cbnfocus ++ dualize

generateCodeActionCommandDeclaration :: TextDocumentIdentifier -> TST.CommandDeclaration -> [Command |? CodeAction]
generateCodeActionCommandDeclaration ident decl@TST.MkCommandDeclaration {cmddecl_cmd } =
  let
    desugar = [ generateCmdDesugarCodeAction ident decl | not (isDesugaredCommand cmddecl_cmd)]
    cbvfocus = [ generateCmdFocusCodeAction ident CBV decl | isDesugaredCommand cmddecl_cmd, isNothing (isFocusedCmd CBV cmddecl_cmd)]
    cbnfocus = [ generateCmdFocusCodeAction ident CBN decl | isDesugaredCommand cmddecl_cmd, isNothing (isFocusedCmd CBN cmddecl_cmd)]
  in
    desugar ++ cbvfocus ++ cbnfocus

generateCodeAction :: TextDocumentIdentifier -> Range -> TST.Declaration -> [Command |? CodeAction]
generateCodeAction ident Range {_start = start } (TST.PrdCnsDecl _ decl) | lookupPos start (TST.pcdecl_loc decl) =
  generateCodeActionPrdCnsDeclaration ident decl
generateCodeAction ident Range {_start = start} (TST.CmdDecl decl) | lookupPos start (TST.cmddecl_loc decl) =
  generateCodeActionCommandDeclaration ident decl
generateCodeAction ident Range {_start = _start} (TST.DataDecl decl) = dualizeDecl
  where     
    dualizeDecl = [generateDualizeDeclCodeAction ident (RST.data_loc decl) decl]
generateCodeAction _ _ _ = []

---------------------------------------------------------------------------------
-- Provide TypeAnnot Action
---------------------------------------------------------------------------------

generateAnnotCodeAction :: forall pc. TextDocumentIdentifier -> TST.PrdCnsDeclaration pc -> Command |? CodeAction
generateAnnotCodeAction (TextDocumentIdentifier uri) decl =
  InR $ CodeAction { _title = "Annotate type for " <> ppPrint (TST.pcdecl_name decl)
                   , _kind = Just CodeActionQuickFix
                   , _diagnostics = Nothing
                   , _isPreferred = Nothing
                   , _disabled = Nothing
                   , _edit = Just (generateAnnotEdit uri decl)
                   , _command = Nothing
                   , _xdata = Nothing
                   }

generateAnnotEdit :: forall pc. Uri -> TST.PrdCnsDeclaration pc -> WorkspaceEdit
generateAnnotEdit uri (TST.MkPrdCnsDeclaration loc doc rep isrec fv (Inferred tys) tm) =
  let
    newDecl :: TST.Declaration
    newDecl = TST.PrdCnsDecl rep (TST.MkPrdCnsDeclaration loc doc rep isrec fv (Annotated tys) tm)
    replacement = ppPrint newDecl
    edit = TextEdit {_range = locToRange loc, _newText = replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing }
generateAnnotEdit _ TST.MkPrdCnsDeclaration { pcdecl_annot = Annotated _ } = error "Should not occur"

---------------------------------------------------------------------------------
-- Provide Dualize Action
---------------------------------------------------------------------------------

generateDualizeCodeAction :: forall pc. TextDocumentIdentifier -> TST.PrdCnsDeclaration pc -> Command |? CodeAction
generateDualizeCodeAction (TextDocumentIdentifier uri) decl =
  InR $ CodeAction { _title = "Dualize term " <> ppPrint (TST.pcdecl_name decl)
                   , _kind = Just CodeActionQuickFix
                   , _diagnostics = Nothing
                   , _isPreferred = Nothing
                   , _disabled = Nothing
                   , _edit = Just (generateDualizeEdit uri decl)
                   , _command = Nothing
                   , _xdata = Nothing
                   }


generateDualizeEdit :: forall pc. Uri -> TST.PrdCnsDeclaration pc -> WorkspaceEdit
generateDualizeEdit uri (TST.MkPrdCnsDeclaration loc doc rep isrec fv (Annotated tys) tm) =
  let
    tm' = dualTerm rep tm
    replacement = case tm' of
      (Left error) -> ppPrint $ pack (show error)
      (Right tm'') -> case rep of
        PrdRep -> ppPrint (TST.PrdCnsDecl CnsRep (TST.MkPrdCnsDeclaration loc doc CnsRep isrec (dualFVName fv) (Annotated (dualTypeScheme PosRep tys)) tm''))
        CnsRep -> ppPrint (TST.PrdCnsDecl PrdRep (TST.MkPrdCnsDeclaration loc doc PrdRep isrec (dualFVName fv) (Annotated (dualTypeScheme NegRep tys)) tm''))
    edit = TextEdit {_range = locToEndRange loc, _newText = pack "\n" `append` replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing }
generateDualizeEdit _ TST.MkPrdCnsDeclaration { pcdecl_annot = Inferred _ } = error "Should not occur"

generateDualizeDeclCodeAction :: TextDocumentIdentifier -> Loc -> RST.DataDecl -> Command |? CodeAction
generateDualizeDeclCodeAction (TextDocumentIdentifier uri) loc decl =
  InR $ CodeAction { _title = "Dualize declaration " <> ppPrint (RST.data_name decl)
                   , _kind = Just CodeActionQuickFix
                   , _diagnostics = Nothing
                   , _isPreferred = Nothing
                   , _disabled = Nothing
                   , _edit = Just (generateDualizeDeclEdit uri loc decl)
                   , _command = Nothing
                   , _xdata = Nothing
                   }


generateDualizeDeclEdit :: Uri -> Loc -> RST.DataDecl -> WorkspaceEdit
generateDualizeDeclEdit uri loc decl =
  let
    decl' = dualDataDecl decl
    replacement = ppPrint (TST.DataDecl decl')
    edit = TextEdit {_range = locToEndRange loc, _newText = pack "\n" `append` replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing }


---------------------------------------------------------------------------------
-- Provide Focus Actions
---------------------------------------------------------------------------------


generateFocusCodeAction :: forall pc.TextDocumentIdentifier -> EvaluationOrder -> TST.PrdCnsDeclaration pc -> Command |? CodeAction
generateFocusCodeAction ident eo decl =
  InR $ CodeAction { _title = "Focus " <> (case eo of CBV -> "CBV "; CBN -> "CBN ") <> unFreeVarName (TST.pcdecl_name decl)
                   , _kind = Just CodeActionQuickFix
                   , _diagnostics = Nothing
                   , _isPreferred = Nothing
                   , _disabled = Nothing
                   , _edit = Just (generateFocusEdit ident eo decl)
                   , _command = Nothing
                   , _xdata = Nothing
                   }

generateFocusEdit :: forall pc.TextDocumentIdentifier -> EvaluationOrder -> TST.PrdCnsDeclaration pc -> WorkspaceEdit
generateFocusEdit (TextDocumentIdentifier uri) eo decl =
  let
    newDecl :: TST.Declaration
    newDecl = TST.PrdCnsDecl (TST.pcdecl_pc decl) (focusPrdCnsDeclaration eo decl)
    replacement = ppPrint newDecl
    edit = TextEdit {_range = locToRange (TST.pcdecl_loc decl), _newText = replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }

generateCmdFocusCodeAction :: TextDocumentIdentifier -> EvaluationOrder -> TST.CommandDeclaration -> Command |? CodeAction
generateCmdFocusCodeAction ident eo decl =
  InR $ CodeAction { _title = "Focus " <> (case eo of CBV -> "CBV "; CBN -> "CBN ") <> unFreeVarName (TST.cmddecl_name decl)
                   , _kind = Just CodeActionQuickFix
                   , _diagnostics = Nothing
                   , _isPreferred = Nothing
                   , _disabled = Nothing
                   , _edit = Just (generateCmdFocusEdit ident eo decl)
                   , _command = Nothing
                   , _xdata = Nothing
                   }

generateCmdFocusEdit :: TextDocumentIdentifier -> EvaluationOrder -> TST.CommandDeclaration -> WorkspaceEdit
generateCmdFocusEdit (TextDocumentIdentifier uri) eo decl =
  let
    newDecl = TST.CmdDecl (focusCommandDeclaration eo decl)
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

generateDesugarCodeAction :: forall pc. TextDocumentIdentifier -> TST.PrdCnsDeclaration pc -> Command |? CodeAction
generateDesugarCodeAction ident decl =
  InR $ CodeAction { _title = "Desugar " <> unFreeVarName (TST.pcdecl_name decl)
                   , _kind = Just CodeActionQuickFix
                   , _diagnostics = Nothing
                   , _isPreferred = Nothing
                   , _disabled = Nothing
                   , _edit = Just (generateDesugarEdit ident decl)
                   , _command = Nothing
                   , _xdata = Nothing
                   }

generateDesugarEdit :: forall pc. TextDocumentIdentifier  -> TST.PrdCnsDeclaration pc -> WorkspaceEdit
generateDesugarEdit (TextDocumentIdentifier uri) (TST.MkPrdCnsDeclaration loc doc rep isRec name (Annotated ty) tm) =
  let
    newDecl = TST.PrdCnsDecl rep (TST.MkPrdCnsDeclaration defaultLoc doc rep isRec name (Annotated ty) (resetAnnotationTerm tm))
    replacement = ppPrint newDecl
    edit = TextEdit {_range =locToRange loc, _newText = replacement}
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing}
generateDesugarEdit _ TST.MkPrdCnsDeclaration { pcdecl_annot = Inferred _ } = error "Should not occur"

generateCmdDesugarCodeAction ::  TextDocumentIdentifier -> TST.CommandDeclaration -> Command |? CodeAction
generateCmdDesugarCodeAction ident decl =
  InR $ CodeAction { _title = "Desugar " <> unFreeVarName (TST.cmddecl_name decl)
                   , _kind = Just CodeActionQuickFix
                   , _diagnostics = Nothing
                   , _isPreferred = Nothing
                   , _disabled = Nothing
                   , _edit = Just (generateCmdDesugarEdit ident decl)
                   , _command = Nothing
                   , _xdata = Nothing
                   }

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
