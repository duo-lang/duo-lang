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
import LSP.MegaparsecToLSP ( locToRange, lookupPos, locToEndRange )
import Syntax.RST.Types ( TypeScheme, TopAnnot(..))
import Syntax.CST.Kinds ( EvaluationOrder(..) )
import Syntax.Common.Names
    ( DocComment,
      FreeVarName(unFreeVarName),
      ModuleName(MkModuleName) )
import Syntax.Common.PrdCns ( PrdCnsRep(..), PrdCnsToPol )
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Program qualified as TST
import Syntax.RST.Program qualified as RST
import Syntax.CST.Program qualified as CST
import Driver.Definition
import Driver.Driver ( inferProgramIO )
import Utils
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint )
import Pretty.Program ()
import Translate.Focusing ( focusTerm, isFocusedTerm, isFocusedCmd, focusCmd )
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
      (res,_warnings) <- liftIO $ inferProgramIO defaultDriverState (MkModuleName (getUri uri)) decls
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
generateCodeActionPrdCnsDeclaration ident TST.MkPrdCnsDeclaration {pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot = Annotated tys, pcdecl_term } =
  let
    desugar  = [ generateDesugarCodeAction pcdecl_pc ident (pcdecl_name, (pcdecl_term, pcdecl_loc, tys)) | not (isDesugaredTerm pcdecl_term)]
    cbvfocus = [ generateFocusCodeAction pcdecl_pc ident CBV (pcdecl_name, (pcdecl_term, pcdecl_loc, tys)) | isDesugaredTerm pcdecl_term, isNothing (isFocusedTerm CBV pcdecl_term)]
    cbnfocus = [ generateFocusCodeAction pcdecl_pc ident CBN (pcdecl_name, (pcdecl_term, pcdecl_loc, tys)) | isDesugaredTerm pcdecl_term, isNothing (isFocusedTerm CBN pcdecl_term)]
    dualize = [generateDualizeCodeAction ident pcdecl_loc pcdecl_doc pcdecl_pc pcdecl_isRec pcdecl_name tys pcdecl_term]
  in
    desugar ++ cbvfocus ++ cbnfocus ++ dualize

generateCodeActionCommandDeclaration :: TextDocumentIdentifier -> TST.CommandDeclaration -> [Command |? CodeAction]
generateCodeActionCommandDeclaration ident TST.MkCommandDeclaration {cmddecl_loc, cmddecl_name, cmddecl_cmd } =
  let
    desugar = [ generateCmdDesugarCodeAction ident (cmddecl_name, (cmddecl_cmd, cmddecl_loc)) | not (isDesugaredCommand cmddecl_cmd)]
    cbvfocus = [ generateCmdFocusCodeAction ident CBV (cmddecl_name, (cmddecl_cmd, cmddecl_loc)) | isDesugaredCommand cmddecl_cmd, isNothing (isFocusedCmd CBV cmddecl_cmd)]
    cbnfocus = [ generateCmdFocusCodeAction ident CBN (cmddecl_name, (cmddecl_cmd, cmddecl_loc)) | isDesugaredCommand cmddecl_cmd, isNothing (isFocusedCmd CBN cmddecl_cmd)]
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
generateDualizeCodeAction :: TextDocumentIdentifier -> Loc -> Maybe DocComment -> PrdCnsRep pc -> CST.IsRec -> FreeVarName -> TypeScheme (PrdCnsToPol pc) -> TST.Term pc -> Command |? CodeAction
generateDualizeCodeAction (TextDocumentIdentifier uri) loc doc rep isrec fv tys tm = InR $ CodeAction { _title = "Dualize term " <> ppPrint fv
                                                                             , _kind = Just CodeActionQuickFix
                                                                             , _diagnostics = Nothing
                                                                             , _isPreferred = Nothing
                                                                             , _disabled = Nothing
                                                                             , _edit = Just (generateDualizeEdit uri loc doc rep isrec fv tys tm)
                                                                             , _command = Nothing
                                                                             , _xdata = Nothing
                                                                             }


generateDualizeEdit :: Uri -> Loc -> Maybe DocComment -> PrdCnsRep pc -> CST.IsRec -> FreeVarName -> TypeScheme (PrdCnsToPol pc) -> TST.Term pc -> WorkspaceEdit
generateDualizeEdit uri loc doc rep isrec fv tys tm  =
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


generateDualizeDeclCodeAction :: TextDocumentIdentifier -> Loc -> RST.DataDecl -> Command |? CodeAction
generateDualizeDeclCodeAction (TextDocumentIdentifier uri) loc decl = InR $ CodeAction { _title = "Dualize declaration " <> ppPrint (RST.data_name decl)
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


generateFocusCodeAction :: PrdCnsRep pc -> TextDocumentIdentifier -> EvaluationOrder -> (FreeVarName, (TST.Term pc, Loc, TypeScheme (PrdCnsToPol pc))) -> Command |? CodeAction
generateFocusCodeAction rep ident eo arg@(name, _) = InR $ CodeAction { _title = "Focus " <> (case eo of CBV -> "CBV "; CBN -> "CBN ") <> unFreeVarName name
                                                                  , _kind = Just CodeActionQuickFix
                                                                  , _diagnostics = Nothing
                                                                  , _isPreferred = Nothing
                                                                  , _disabled = Nothing
                                                                  , _edit = Just (generateFocusEdit rep eo ident arg)
                                                                  , _command = Nothing
                                                                  , _xdata = Nothing
                                                                  }

generateFocusEdit :: PrdCnsRep pc -> EvaluationOrder -> TextDocumentIdentifier ->  (FreeVarName, (TST.Term pc, Loc, TypeScheme (PrdCnsToPol pc))) -> WorkspaceEdit
generateFocusEdit pc eo (TextDocumentIdentifier uri) (name,(tm,loc,ty)) =
  let
    newDecl :: TST.Declaration = case pc of
                PrdRep -> TST.PrdCnsDecl PrdRep (TST.MkPrdCnsDeclaration defaultLoc Nothing PrdRep CST.Recursive name (Inferred ty) (focusTerm eo (resetAnnotationTerm tm)))
                CnsRep -> TST.PrdCnsDecl CnsRep (TST.MkPrdCnsDeclaration defaultLoc Nothing CnsRep CST.Recursive name (Inferred ty) (focusTerm eo (resetAnnotationTerm tm)))
    replacement = ppPrint newDecl
    edit = TextEdit {_range= locToRange loc, _newText= replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }

generateCmdFocusCodeAction :: TextDocumentIdentifier -> EvaluationOrder -> (FreeVarName, (TST.Command, Loc)) -> Command |? CodeAction
generateCmdFocusCodeAction ident eo arg@(name, _) = InR $ CodeAction { _title = "Focus " <> (case eo of CBV -> "CBV "; CBN -> "CBN ") <> unFreeVarName name
                                                                  , _kind = Just CodeActionQuickFix
                                                                  , _diagnostics = Nothing
                                                                  , _isPreferred = Nothing
                                                                  , _disabled = Nothing
                                                                  , _edit = Just (generateCmdFocusEdit eo ident arg)
                                                                  , _command = Nothing
                                                                  , _xdata = Nothing
                                                                  }

generateCmdFocusEdit ::  EvaluationOrder -> TextDocumentIdentifier ->  (FreeVarName, (TST.Command, Loc)) -> WorkspaceEdit
generateCmdFocusEdit eo (TextDocumentIdentifier uri) (name,(cmd,loc)) =
  let
    newDecl = TST.CmdDecl (TST.MkCommandDeclaration defaultLoc Nothing name (focusCmd eo (resetAnnotationCmd cmd)))
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

generateDesugarCodeAction :: PrdCnsRep pc -> TextDocumentIdentifier -> (FreeVarName,(TST.Term pc, Loc, TypeScheme (PrdCnsToPol pc))) -> Command |? CodeAction
generateDesugarCodeAction rep ident arg@(name,_) = InR $ CodeAction { _title = "Desugar " <> unFreeVarName name
                                                                    , _kind = Just CodeActionQuickFix
                                                                    , _diagnostics = Nothing
                                                                    , _isPreferred = Nothing
                                                                    , _disabled = Nothing
                                                                    , _edit = Just (generateDesugarEdit rep ident arg)
                                                                    , _command = Nothing
                                                                    , _xdata = Nothing
                                                                    }

generateDesugarEdit :: PrdCnsRep pc -> TextDocumentIdentifier  -> (FreeVarName,(TST.Term pc, Loc, TypeScheme (PrdCnsToPol pc))) -> WorkspaceEdit
generateDesugarEdit rep (TextDocumentIdentifier uri) (name, (tm,loc,ty)) =
  let
    newDecl = TST.PrdCnsDecl rep (TST.MkPrdCnsDeclaration defaultLoc Nothing rep CST.Recursive name (Inferred ty) (resetAnnotationTerm tm))
    replacement = ppPrint newDecl
    edit = TextEdit {_range=locToRange loc, _newText=replacement}
  in
    WorkspaceEdit { _changes= Just (Map.singleton uri (List [edit]))
                  , _documentChanges=Nothing
                  , _changeAnnotations=Nothing}

generateCmdDesugarCodeAction ::  TextDocumentIdentifier -> (FreeVarName, (TST.Command, Loc)) -> Command |? CodeAction
generateCmdDesugarCodeAction ident arg@(name,_) = InR $ CodeAction { _title = "Desugar " <> unFreeVarName name
                                                                   , _kind = Just CodeActionQuickFix
                                                                   , _diagnostics = Nothing
                                                                   , _isPreferred = Nothing
                                                                   , _disabled = Nothing
                                                                   , _edit = Just (generateCmdDesugarEdit ident arg)
                                                                   , _command = Nothing
                                                                   , _xdata = Nothing
                                                                   }

generateCmdDesugarEdit :: TextDocumentIdentifier -> (FreeVarName, (TST.Command, Loc)) -> WorkspaceEdit
generateCmdDesugarEdit (TextDocumentIdentifier uri) (name, (cmd,loc)) =
  let
    newDecl = TST.CmdDecl (TST.MkCommandDeclaration defaultLoc Nothing name (resetAnnotationCmd cmd))
    replacement = ppPrint newDecl
    edit = TextEdit {_range = locToRange loc, _newText= replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }
