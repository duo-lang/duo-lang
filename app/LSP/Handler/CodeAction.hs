{-# LANGUAGE TypeOperators #-}
module LSP.Handler.CodeAction (codeActionHandler) where

import Control.Monad (join)
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.HashMap.Strict qualified as Map
import Data.Maybe ( fromMaybe, isNothing )
import Data.Text qualified as T
import Language.LSP.Types
import Language.LSP.Server
import Language.LSP.VFS
import System.Log.Logger ( debugM )
import Syntax.TST.Types qualified as TST ( TopAnnot(..))
import Syntax.RST.Types ( PolarityRep(..))
import Syntax.CST.Kinds ( EvaluationOrder(..) )
import Syntax.TST.Program qualified as TST
import Syntax.RST.Program qualified as RST
import Syntax.CST.Types (PrdCnsRep(..))
import Driver.Definition
import Driver.Driver ( inferProgramIO )
import Dualize.Program (dualDataDecl)
import Dualize.Terms (dualTerm, dualTypeScheme, dualFVName)
import LSP.Definition ( LSPMonad )
import LSP.MegaparsecToLSP ( locToRange, lookupPos, locToEndRange, locToStartRange )
import Parser.Definition ( runFileParser )
import Parser.Program ( moduleP )
import Pretty.Pretty ( ppPrint )
import Pretty.Program ()
import Sugar.TST (isDesugaredTerm, isDesugaredCommand, resetAnnotationTerm, resetAnnotationCmd)
import Syntax.CST.Names ( FreeVarName(..) )
import Translate.Focusing ( Focus(..) )
import Loc
import Eval.Eval (eval, EvalMWrapper (..))
import qualified Syntax.TST.Terms as TST
import Errors (Error)
import Data.List.NonEmpty (NonEmpty)
import Control.Monad.State.Strict (StateT, execStateT)
import Control.Monad.Writer.Strict (Writer, execWriter)

---------------------------------------------------------------------------------
-- Provide CodeActions
---------------------------------------------------------------------------------

codeActionHandler :: Handlers LSPMonad
codeActionHandler = requestHandler STextDocumentCodeAction $ \req responder -> do
  let (RequestMessage _ _ _ (CodeActionParams _workDoneToken _partialResultToken ident@(TextDocumentIdentifier uri) range _context)) = req
  liftIO $ debugM "lspserver.codeActionHandler" ("Received codeAction request: " <> show uri <> " range: " <> show range)
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
          responder (Right (generateCodeActions ident range prog))

generateCodeActions :: TextDocumentIdentifier -> Range -> TST.Module -> List (Command  |? CodeAction)
generateCodeActions ident rng TST.MkModule { mod_decls } = List (join ls)
  where
    ls = generateCodeAction ident rng <$> mod_decls


generateCodeActionPrdCnsDeclaration :: TextDocumentIdentifier -> TST.PrdCnsDeclaration pc -> [Command |? CodeAction]
generateCodeActionPrdCnsDeclaration ident decl@TST.MkPrdCnsDeclaration { pcdecl_annot = TST.Inferred _ } =
  [generateAnnotCodeAction ident decl]
generateCodeActionPrdCnsDeclaration ident decl@TST.MkPrdCnsDeclaration { pcdecl_annot = TST.Annotated _, pcdecl_term } =
  let
    desugar  = [ generateDesugarCodeAction ident decl | not (isDesugaredTerm pcdecl_term)]
    cbvfocus = [ generateFocusCodeAction ident CBV decl | isDesugaredTerm pcdecl_term, isNothing (isFocused CBV pcdecl_term)]
    cbnfocus = [ generateFocusCodeAction ident CBN decl | isDesugaredTerm pcdecl_term, isNothing (isFocused CBN pcdecl_term)]
    dualize  = [ generateDualizeCodeAction ident decl]
  in
    desugar ++ cbvfocus ++ cbnfocus ++ dualize

generateCodeActionCommandDeclaration :: TextDocumentIdentifier -> TST.CommandDeclaration -> [Command |? CodeAction]
generateCodeActionCommandDeclaration ident decl@TST.MkCommandDeclaration {cmddecl_cmd } =
  let
    desugar  = [ generateCmdDesugarCodeAction ident decl | not (isDesugaredCommand cmddecl_cmd)]
    cbvfocus = [ generateCmdFocusCodeAction ident CBV decl | isDesugaredCommand cmddecl_cmd, isNothing (isFocused CBV cmddecl_cmd)]
    cbnfocus = [ generateCmdFocusCodeAction ident CBN decl | isDesugaredCommand cmddecl_cmd, isNothing (isFocused CBN cmddecl_cmd)]
    eval     = [ generateCmdEvalCodeAction ident decl ]
  in
    desugar ++ cbvfocus ++ cbnfocus ++ eval

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
generateAnnotEdit uri (TST.MkPrdCnsDeclaration loc doc rep isrec fv (TST.Inferred tys) tm) =
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
generateDualizeEdit uri (TST.MkPrdCnsDeclaration loc doc rep isrec fv (TST.Annotated tys) tm) =
  let
    tm' = dualTerm rep tm
    replacement = case tm' of
      (Left error) -> ppPrint $ T.pack (show error)
      (Right tm'') -> case rep of
        PrdRep -> ppPrint (TST.PrdCnsDecl CnsRep (TST.MkPrdCnsDeclaration loc doc CnsRep isrec (dualFVName fv) (TST.Annotated (dualTypeScheme PosRep tys)) tm''))
        CnsRep -> ppPrint (TST.PrdCnsDecl PrdRep (TST.MkPrdCnsDeclaration loc doc PrdRep isrec (dualFVName fv) (TST.Annotated (dualTypeScheme NegRep tys)) tm''))
    edit = TextEdit {_range = locToEndRange loc, _newText = T.pack "\n" `T.append` replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing }
generateDualizeEdit _ TST.MkPrdCnsDeclaration { pcdecl_annot = TST.Inferred _ } = error "Should not occur"

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
    edit = TextEdit {_range = locToEndRange loc, _newText = T.pack "\n" `T.append` replacement }
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
    newDecl = TST.PrdCnsDecl (TST.pcdecl_pc decl) (focus eo decl)
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

generateCmdEvalCodeAction ::  TextDocumentIdentifier -> TST.CommandDeclaration -> Command |? CodeAction
generateCmdEvalCodeAction ident decl =
  InR $ CodeAction { _title = "Eval " <> unFreeVarName (TST.cmddecl_name decl)
                   , _kind = Just CodeActionQuickFix
                   , _diagnostics = Nothing
                   , _isPreferred = Nothing
                   , _disabled = Nothing
                   , _edit = Just (generateCmdEvalEdit ident decl)
                   , _command = Nothing
                   , _xdata = Nothing
                   }

generateCmdEvalEdit :: TextDocumentIdentifier -> TST.CommandDeclaration -> WorkspaceEdit
generateCmdEvalEdit (TextDocumentIdentifier uri) decl =
  let
    evalEnv = undefined
    result = execWriter $ flip execStateT [] $ unEvalMWrapper (eval (TST.cmddecl_cmd decl) evalEnv :: EvalMWrapper (StateT [Int] (Writer [String])) (Either (NonEmpty Error) TST.Command))
    replacement = T.pack $ unlines result ++ "\n"
    edit = TextEdit {_range = locToStartRange (TST.cmddecl_loc decl), _newText = replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }

