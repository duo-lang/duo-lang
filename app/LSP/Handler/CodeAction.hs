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
import Syntax.Common.TypesPol ( TypeScheme, TopAnnot(..) )
import Syntax.Common.Kinds ( EvaluationOrder(..) )
import Syntax.Common.Names
    ( DocComment,
      FreeVarName(unFreeVarName),
      ModuleName(MkModuleName) )
import Syntax.Common.PrdCns ( PrdCnsRep(..), PrdCnsToPol, flipPrdCns )
import Syntax.Common.Types ( IsRec(Recursive) )
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Program qualified as TST
--import Syntax.Core.Program qualified as Core
import Driver.Definition
import Driver.Driver ( inferProgramIO )
import Utils
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint )
import Pretty.Program ()
import Translate.Focusing ( focusTerm, isFocusedTerm, isFocusedCmd, focusCmd )
import Sugar.AST (isDesugaredTerm, isDesugaredCommand, resetAnnotationTerm, resetAnnotationCmd)
import Dualize.Terms (dualTerm, dualTypeScheme)
import Syntax.Common.Polarity
import Data.Text (pack)
import qualified Debug.Trace

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

generateCodeActions :: TextDocumentIdentifier -> Range -> TST.Program -> List (Command  |? CodeAction)
generateCodeActions ident rng program = List (join ls)
  where
    ls = generateCodeAction ident rng <$> program


generateCodeAction :: TextDocumentIdentifier -> Range -> TST.Declaration -> [Command |? CodeAction]
generateCodeAction ident (Range {_start = start }) (TST.PrdCnsDecl loc doc rep isrec fv (Inferred tys) tm) | lookupPos start loc =
  [generateAnnotCodeAction ident loc doc rep isrec fv tys tm,generateDualizeCodeAction ident loc doc rep isrec fv tys tm ]
generateCodeAction ident (Range {_start = start }) (TST.PrdCnsDecl loc doc rep isrec fv (Annotated tys) tm) = desugar ++ cbvfocus ++ cbnfocus ++ dualize
  where
    desugar  = [ generateDesugarCodeAction rep ident (fv, (tm, loc, tys)) | not (isDesugaredTerm tm), lookupPos start loc]
    cbvfocus = [ generateFocusCodeAction rep ident CBV (fv, (tm, loc, tys)) | isDesugaredTerm tm, isNothing (isFocusedTerm CBV tm), lookupPos start loc]
    cbnfocus = [ generateFocusCodeAction rep ident CBN (fv, (tm, loc, tys)) | isDesugaredTerm tm, isNothing (isFocusedTerm CBV tm), lookupPos start loc]
    dualize = [generateDualizeCodeAction ident loc doc rep isrec fv tys tm]
generateCodeAction ident (Range {_start = start}) (TST.CmdDecl loc _doc fv cmd) = desugar ++ cbvfocus ++ cbnfocus  
  where
    desugar = [ generateCmdDesugarCodeAction ident (fv, (cmd, loc)) | not (isDesugaredCommand cmd), lookupPos start loc]
    cbvfocus = [ generateCmdFocusCodeAction ident CBN (fv, (cmd,loc)) | isDesugaredCommand cmd, isNothing (isFocusedCmd CBN cmd), lookupPos start loc]
    cbnfocus = [ generateCmdFocusCodeAction ident CBN (fv, (cmd,loc)) | isDesugaredCommand cmd, isNothing (isFocusedCmd CBN cmd), lookupPos start loc]
    
generateCodeAction _ _ _ = []

---------------------------------------------------------------------------------
-- Provide TypeAnnot Action
---------------------------------------------------------------------------------

generateAnnotCodeAction :: TextDocumentIdentifier -> Loc -> Maybe DocComment -> PrdCnsRep pc -> IsRec -> FreeVarName -> TypeScheme (PrdCnsToPol pc) -> TST.Term pc -> Command |? CodeAction
generateAnnotCodeAction (TextDocumentIdentifier uri) loc doc rep isrec fv tys tm = InR $ CodeAction { _title = "Annotate type for " <> ppPrint fv
                                                                             , _kind = Just CodeActionQuickFix
                                                                             , _diagnostics = Nothing
                                                                             , _isPreferred = Nothing
                                                                             , _disabled = Nothing
                                                                             , _edit = Just (generateAnnotEdit uri loc doc rep isrec fv tys tm)
                                                                             , _command = Nothing
                                                                             , _xdata = Nothing
                                                                             }
generateAnnotEdit :: Uri -> Loc -> Maybe DocComment -> PrdCnsRep pc -> IsRec -> FreeVarName -> TypeScheme (PrdCnsToPol pc) -> TST.Term pc -> WorkspaceEdit
generateAnnotEdit uri loc doc rep isrec fv tys tm  =
  let
    newDecl :: TST.Declaration = TST.PrdCnsDecl loc doc rep isrec fv (Annotated tys) tm
    replacement = ppPrint newDecl
    edit = TextEdit {_range = locToRange loc, _newText = replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing }


---------------------------------------------------------------------------------
-- Provide Dualize Action
---------------------------------------------------------------------------------
generateDualizeCodeAction :: TextDocumentIdentifier -> Loc -> Maybe DocComment -> PrdCnsRep pc -> IsRec -> FreeVarName -> TypeScheme (PrdCnsToPol pc) -> TST.Term pc -> Command |? CodeAction
generateDualizeCodeAction (TextDocumentIdentifier uri) loc doc rep isrec fv tys tm = InR $ CodeAction { _title = "Dualize term " <> ppPrint fv
                                                                             , _kind = Just CodeActionQuickFix
                                                                             , _diagnostics = Nothing
                                                                             , _isPreferred = Nothing
                                                                             , _disabled = Nothing
                                                                             , _edit = Just (generateDualizeEdit uri loc doc rep isrec fv tys tm)
                                                                             , _command = Nothing
                                                                             , _xdata = Nothing
                                                                             }


generateDualizeEdit :: Uri -> Loc -> Maybe DocComment -> PrdCnsRep pc -> IsRec -> FreeVarName -> TypeScheme (PrdCnsToPol pc) -> TST.Term pc -> WorkspaceEdit
generateDualizeEdit uri loc doc rep isrec fv tys tm  =
  let
    tm' = dualTerm rep tm
    replacement = case tm' of
      (Left error) -> ppPrint $ pack (show error)
      (Right tm'') -> case rep of
        PrdRep -> ppPrint (TST.PrdCnsDecl loc doc CnsRep isrec fv (Annotated (dualTypeScheme PosRep tys)) tm'')
        CnsRep -> ppPrint (TST.PrdCnsDecl loc doc PrdRep isrec fv (Annotated (dualTypeScheme NegRep tys)) tm'')
    edit = TextEdit {_range = locToRange loc, _newText = replacement }
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
                PrdRep -> TST.PrdCnsDecl defaultLoc Nothing PrdRep Recursive name (Inferred ty) (focusTerm eo (resetAnnotationTerm tm))
                CnsRep -> TST.PrdCnsDecl defaultLoc Nothing CnsRep Recursive name (Inferred ty) (focusTerm eo (resetAnnotationTerm tm))
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
    newDecl = TST.CmdDecl defaultLoc Nothing name (focusCmd eo (resetAnnotationCmd cmd))
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
    newDecl = TST.PrdCnsDecl defaultLoc Nothing rep Recursive name (Inferred ty) (resetAnnotationTerm tm)
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
    newDecl = TST.CmdDecl defaultLoc Nothing name (resetAnnotationCmd cmd)
    replacement = ppPrint newDecl
    edit = TextEdit {_range = locToRange loc, _newText= replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }
