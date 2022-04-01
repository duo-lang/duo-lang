{-# LANGUAGE TypeOperators #-}
module LSP.CodeActionHandler (codeActionHandler) where

import Language.LSP.Types
import Language.LSP.Server
import Language.LSP.VFS
import Data.Map qualified as M
import Data.Maybe ( fromMaybe, isNothing )
import System.Log.Logger ( debugM )
import Data.HashMap.Strict qualified as Map
import Control.Monad.IO.Class ( MonadIO(liftIO) )

import LSP.Definition ( LSPMonad )
import LSP.MegaparsecToLSP ( locToRange, lookupPos )
import Syntax.AST.Program
    ( Declaration(PrdCnsDecl,CmdDecl))
import Driver.Environment (Environment(prdEnv, cnsEnv, cmdEnv))
import Syntax.AST.Types ( TypeScheme )
import Syntax.Common
import Syntax.AST.Terms ( Term )
import Syntax.AST.Terms qualified as Syntax
import Driver.Driver
    ( defaultInferenceOptions,
      inferProgramIO,
      DriverState(DriverState),
      InferenceOptions(infOptsLibPath) )
import Utils
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint, NamedRep(NamedRep) )
import Pretty.Program ()
import Translate.Focusing ( focusTerm, isFocusedTerm, isFocusedCmd, focusCmd )
import Translate.Desugar (desugarTerm, desugarCmd, isDesugaredTerm, isDesugaredCommand)
import Translate.Reparse

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
      res <- liftIO $ inferProgramIO (DriverState (defaultInferenceOptions { infOptsLibPath = ["examples"]}) mempty mempty) decls
      case res of
        Left _err -> do
          responder (Right (List []))
        Right (env,_) -> do
          responder (Right (generateCodeActions ident range env))

generateCodeActions :: TextDocumentIdentifier -> Range -> Environment Inferred -> List (Command  |? CodeAction)
generateCodeActions ident (Range {_start= start}) env = do
  -- Producer declarations
  let prds = M.toList $ prdEnv env
  let desugarActionsPrd  = [ generateDesugarCodeAction PrdRep ident prd | prd@(_,(tm,loc,_)) <- prds, not (isDesugaredTerm tm), lookupPos start loc]
  let cbvFocusActionsPrd = [ generateFocusCodeAction PrdRep ident CBV prd | prd@(_,(tm,loc,_)) <- prds, isDesugaredTerm tm, isNothing (isFocusedTerm CBV (desugarTerm tm)), lookupPos start loc]
  let cbnFocusActionsPrd = [ generateFocusCodeAction PrdRep ident CBN prd | prd@(_,(tm,loc,_)) <- prds, isDesugaredTerm tm, isNothing (isFocusedTerm CBN (desugarTerm tm)), lookupPos start loc]
  -- Consumer declarations
  let cnss = M.toList $ cnsEnv env
  let desugarActionsCns  = [ generateDesugarCodeAction CnsRep ident cns | cns@(_,(tm,loc,_)) <- cnss, not (isDesugaredTerm tm), lookupPos start loc]
  let cbvFocusActionsCns = [ generateFocusCodeAction CnsRep ident CBV cns | cns@(_,(tm,loc,_)) <- cnss, isDesugaredTerm tm, isNothing (isFocusedTerm CBV (desugarTerm tm)), lookupPos start loc]
  let cbnFocusActionsCns = [ generateFocusCodeAction CnsRep ident CBN cns | cns@(_,(tm,loc,_)) <- cnss, isDesugaredTerm tm, isNothing (isFocusedTerm CBN (desugarTerm tm)), lookupPos start loc]
  -- Command declarations
  let cmds = M.toList $ cmdEnv env
  let desugarActionsCmd  = [ generateCmdDesugarCodeAction ident cmd | cmd@(_,(command, loc)) <- cmds , not (isDesugaredCommand command), lookupPos start loc]
  let cbvFocusActionsCmd = [ generateCmdFocusCodeAction ident CBV cmd | cmd@(_,(command,loc)) <- cmds, isDesugaredCommand command, isNothing (isFocusedCmd CBV (desugarCmd command)), lookupPos start loc]
  let cbnFocusActionsCmd = [ generateCmdFocusCodeAction ident CBN cmd | cmd@(_,(command,loc)) <- cmds, isDesugaredCommand command, isNothing (isFocusedCmd CBN (desugarCmd command)), lookupPos start loc]
  List $ mconcat [ desugarActionsPrd, cbvFocusActionsPrd, cbnFocusActionsPrd
                 , desugarActionsCns, cbvFocusActionsCns, cbnFocusActionsCns
                 , desugarActionsCmd, cbvFocusActionsCmd, cbnFocusActionsCmd
                 ]

---------------------------------------------------------------------------------
-- Provide Focus Actions
---------------------------------------------------------------------------------


generateFocusCodeAction :: PrdCnsRep pc -> TextDocumentIdentifier -> EvaluationOrder -> (FreeVarName, (Term pc Inferred, Loc, TypeScheme (PrdCnsToPol pc))) -> Command |? CodeAction
generateFocusCodeAction rep ident eo arg@(name, _) = InR $ CodeAction { _title = "Focus " <> (case eo of CBV -> "CBV "; CBN -> "CBN ") <> unFreeVarName name
                                                                  , _kind = Just CodeActionQuickFix
                                                                  , _diagnostics = Nothing
                                                                  , _isPreferred = Nothing
                                                                  , _disabled = Nothing
                                                                  , _edit = Just (generateFocusEdit rep eo ident arg)
                                                                  , _command = Nothing
                                                                  , _xdata = Nothing
                                                                  }

generateFocusEdit :: PrdCnsRep pc -> EvaluationOrder -> TextDocumentIdentifier ->  (FreeVarName, (Term pc Inferred, Loc, TypeScheme (PrdCnsToPol pc))) -> WorkspaceEdit
generateFocusEdit pc eo (TextDocumentIdentifier uri) (name,(tm,loc,ty)) =
  let
    newDecl :: NamedRep (Declaration 'Parsed) = case pc of
                PrdRep -> NamedRep $ PrdCnsDecl (Nothing, defaultLoc) PrdRep Recursive name (Just ty) (reparseTerm (focusTerm eo (desugarTerm tm)))
                CnsRep -> NamedRep $ PrdCnsDecl (Nothing, defaultLoc) CnsRep Recursive name (Just ty) (reparseTerm (focusTerm eo (desugarTerm tm)))
    replacement = ppPrint newDecl
    edit = TextEdit {_range= locToRange loc, _newText= replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }

generateCmdFocusCodeAction :: TextDocumentIdentifier -> EvaluationOrder -> (FreeVarName, (Syntax.Command Inferred, Loc)) -> Command |? CodeAction
generateCmdFocusCodeAction ident eo arg@(name, _) = InR $ CodeAction { _title = "Focus " <> (case eo of CBV -> "CBV "; CBN -> "CBN ") <> unFreeVarName name
                                                                  , _kind = Just CodeActionQuickFix
                                                                  , _diagnostics = Nothing
                                                                  , _isPreferred = Nothing
                                                                  , _disabled = Nothing
                                                                  , _edit = Just (generateCmdFocusEdit eo ident arg)
                                                                  , _command = Nothing
                                                                  , _xdata = Nothing
                                                                  }

generateCmdFocusEdit ::  EvaluationOrder -> TextDocumentIdentifier ->  (FreeVarName, (Syntax.Command Inferred, Loc)) -> WorkspaceEdit
generateCmdFocusEdit eo (TextDocumentIdentifier uri) (name,(cmd,loc)) =
  let
    newDecl = NamedRep $ CmdDecl (Nothing, defaultLoc) name (reparseCommand (focusCmd eo (desugarCmd cmd)))
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

generateDesugarCodeAction :: PrdCnsRep pc -> TextDocumentIdentifier -> (FreeVarName,(Term pc Inferred, Loc, TypeScheme (PrdCnsToPol pc))) -> Command |? CodeAction
generateDesugarCodeAction rep ident arg@(name,_) = InR $ CodeAction { _title = "Desugar " <> unFreeVarName name
                                                                    , _kind = Just CodeActionQuickFix
                                                                    , _diagnostics = Nothing
                                                                    , _isPreferred = Nothing
                                                                    , _disabled = Nothing
                                                                    , _edit = Just (generateDesugarEdit rep ident arg)
                                                                    , _command = Nothing
                                                                    , _xdata = Nothing
                                                                    }

generateDesugarEdit :: PrdCnsRep pc -> TextDocumentIdentifier  -> (FreeVarName,(Term pc Inferred, Loc, TypeScheme (PrdCnsToPol pc))) -> WorkspaceEdit
generateDesugarEdit rep (TextDocumentIdentifier uri) (name, (tm,loc,ty)) =
  let
    newDecl = NamedRep $ reparseDecl $ PrdCnsDecl () rep Recursive name (Just ty) (desugarTerm tm)
    replacement = ppPrint newDecl
    edit = TextEdit {_range=locToRange loc, _newText=replacement}
  in
    WorkspaceEdit { _changes= Just (Map.singleton uri (List [edit]))
                  , _documentChanges=Nothing
                  , _changeAnnotations=Nothing}

generateCmdDesugarCodeAction ::  TextDocumentIdentifier -> (FreeVarName, (Syntax.Command Inferred, Loc)) -> Command |? CodeAction
generateCmdDesugarCodeAction ident arg@(name,_) = InR $ CodeAction { _title = "Desugar " <> unFreeVarName name
                                                                   , _kind = Just CodeActionQuickFix
                                                                   , _diagnostics = Nothing
                                                                   , _isPreferred = Nothing
                                                                   , _disabled = Nothing
                                                                   , _edit = Just (generateCmdDesugarEdit ident arg)
                                                                   , _command = Nothing
                                                                   , _xdata = Nothing
                                                                   }

generateCmdDesugarEdit :: TextDocumentIdentifier -> (FreeVarName, (Syntax.Command Inferred, Loc)) -> WorkspaceEdit
generateCmdDesugarEdit (TextDocumentIdentifier uri) (name, (cmd,loc)) =
  let
    newDecl = NamedRep $ reparseDecl $ CmdDecl () name (desugarCmd cmd)
    replacement = ppPrint newDecl
    edit = TextEdit {_range = locToRange loc, _newText= replacement }
  in
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }
