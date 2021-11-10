{-# LANGUAGE TypeOperators #-}
module LSP.CodeActionHandler (codeActionHandler) where

import Language.LSP.Types
import Language.LSP.Server
import Language.LSP.VFS
import Data.Map qualified as M 
import Data.Maybe ( fromMaybe )
import System.Log.Logger ( debugM )
import Data.HashMap.Strict qualified as Map
import Control.Monad.IO.Class ( MonadIO(liftIO) )

import LSP.Definition ( LSPMonad )
import LSP.MegaparsecToLSP ( locToRange, lookupPos )
import Syntax.Program
    ( Declaration(PrdCnsDecl,CmdDecl), Environment(prdEnv, cnsEnv, cmdEnv), IsRec(Recursive) )
import Syntax.Types ( Polarity(..), TypeScheme)
import Syntax.Kinds (CallingConvention(..))
import Syntax.CommonTerm
import Syntax.Terms ( createNamesSTerm, STerm, createNamesCommand)
import Syntax.Terms qualified as Syntax
import TypeInference.Driver
    ( defaultInferenceOptions,
      inferProgramIO,
      DriverState(DriverState),
      InferenceOptions(infOptsLibPath) )
import Utils ( Loc )
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint, NamedRep(NamedRep) )
import Pretty.Program ()
import Translate.Focusing ( focusSTerm, isFocusedSTerm, isFocusedCmd, focusCmd )
import Translate.Translate ( compile )



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
      res <- liftIO $ inferProgramIO (DriverState (defaultInferenceOptions { infOptsLibPath = ["examples"]}) mempty) decls
      case res of
        Left _err -> do
          responder (Right (List []))
        Right env -> do
          responder (Right (generateCodeActions ident range env))

generateCodeActions :: TextDocumentIdentifier -> Range -> Environment -> List (Command  |? CodeAction)
generateCodeActions ident (Range {_start= start}) env = do
  -- Producer declarations
  let prds = M.toList $ prdEnv env
  let cbvFocusActionsPrd = [ generateFocusCodeAction PrdRep ident CBV prd | prd@(_,(tm,loc,_)) <- prds, not (isFocusedSTerm CBV tm), lookupPos start loc]
  let cbnFocusActionsPrd = [ generateFocusCodeAction PrdRep ident CBN prd | prd@(_,(tm,loc,_)) <- prds, not (isFocusedSTerm CBN tm), lookupPos start loc]
  -- Consumer declarations
  let cnss = M.toList $ cnsEnv env
  let cbvFocusActionsCns = [ generateFocusCodeAction CnsRep ident CBV cns | cns@(_,(tm,loc,_)) <- cnss, not (isFocusedSTerm CBV tm), lookupPos start loc]
  let cbnFocusActionsCns = [ generateFocusCodeAction CnsRep ident CBN cns | cns@(_,(tm,loc,_)) <- cnss, not (isFocusedSTerm CBN tm), lookupPos start loc]
  -- Command declarations
  let cmds = M.toList $ cmdEnv env
  let cbvFocusActionsCmd = [ generateCmdFocusCodeAction ident CBV cmd | cmd@(_,(command,loc)) <- cmds, not (isFocusedCmd CBV command), lookupPos start loc]
  let cbnFocusActionsCmd = [ generateCmdFocusCodeAction ident CBN cmd | cmd@(_,(command,loc)) <- cmds, not (isFocusedCmd CBN command), lookupPos start loc]
  List (cbvFocusActionsPrd <> cbnFocusActionsPrd <> cbvFocusActionsCns <> cbnFocusActionsCns <> cbvFocusActionsCmd <> cbnFocusActionsCmd)

---------------------------------------------------------------------------------
-- Provide Focus Actions
---------------------------------------------------------------------------------

type family Foo (pc :: PrdCns) :: Polarity where
  Foo Prd = Pos 
  Foo Cns = Neg

generateFocusCodeAction :: PrdCnsRep pc -> TextDocumentIdentifier -> CallingConvention -> (FreeVarName, (STerm pc Inferred, Loc, TypeScheme (Foo pc))) -> Command |? CodeAction
generateFocusCodeAction rep ident eo arg@(name, _) = InR $ CodeAction { _title = "Focus " <> (case eo of CBV -> "CBV "; CBN -> "CBN ") <> name
                                                                  , _kind = Just CodeActionQuickFix 
                                                                  , _diagnostics = Nothing
                                                                  , _isPreferred = Nothing
                                                                  , _disabled = Nothing
                                                                  , _edit = Just (generateFocusEdit rep eo ident arg)
                                                                  , _command = Nothing
                                                                  , _xdata = Nothing
                                                                  }

                                      

generateFocusEdit :: PrdCnsRep pc -> CallingConvention -> TextDocumentIdentifier ->  (FreeVarName, (STerm pc Inferred, Loc, TypeScheme (Foo pc))) -> WorkspaceEdit
generateFocusEdit pc eo (TextDocumentIdentifier uri) (name,(tm,loc,ty)) =
  let
    newDecl :: NamedRep (Declaration 'Compiled) = case pc of
                PrdRep -> NamedRep $ PrdCnsDecl () PrdRep Recursive name (Just ty) (createNamesSTerm (focusSTerm eo tm))
                CnsRep -> NamedRep $ PrdCnsDecl () CnsRep Recursive name (Just ty) (createNamesSTerm (focusSTerm eo tm))
    replacement = ppPrint newDecl
    edit = TextEdit {_range= locToRange loc, _newText= replacement }
  in 
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }


generateCmdFocusCodeAction :: TextDocumentIdentifier -> CallingConvention -> (FreeVarName, (Syntax.Command Inferred, Loc)) -> Command |? CodeAction
generateCmdFocusCodeAction ident eo arg@(name, _) = InR $ CodeAction { _title = "Focus " <> (case eo of CBV -> "CBV "; CBN -> "CBN ") <> name
                                                                  , _kind = Just CodeActionQuickFix 
                                                                  , _diagnostics = Nothing
                                                                  , _isPreferred = Nothing
                                                                  , _disabled = Nothing
                                                                  , _edit = Just (generateCmdFocusEdit eo ident arg)
                                                                  , _command = Nothing
                                                                  , _xdata = Nothing
                                                                  }

generateCmdFocusEdit ::  CallingConvention -> TextDocumentIdentifier ->  (FreeVarName, (Syntax.Command Inferred, Loc)) -> WorkspaceEdit
generateCmdFocusEdit eo (TextDocumentIdentifier uri) (name,(cmd,loc)) =
  let
    newDecl = NamedRep $ CmdDecl () name (createNamesCommand (focusCmd eo cmd))
    replacement = ppPrint newDecl
    edit = TextEdit {_range= locToRange loc, _newText= replacement }
  in 
    WorkspaceEdit { _changes = Just (Map.singleton uri (List [edit]))
                  , _documentChanges = Nothing
                  , _changeAnnotations = Nothing
                  }
---------------------------------------------------------------------------------
-- Provide Translation Actions
---------------------------------------------------------------------------------

generateTranslateCodeAction :: TextDocumentIdentifier -> (FreeVarName,(STerm Prd Inferred, Loc, TypeScheme Pos)) -> Command |? CodeAction
generateTranslateCodeAction ident arg@(name,_) = InR $ CodeAction { _title = "Translate " <> name
                                                                  , _kind = Just CodeActionQuickFix 
                                                                  , _diagnostics = Nothing
                                                                  , _isPreferred = Nothing
                                                                  , _disabled = Nothing
                                                                  , _edit = Just (generateTranslateEdit ident arg)
                                                                  , _command = Nothing
                                                                  , _xdata = Nothing
                                                                  }

generateTranslateEdit :: TextDocumentIdentifier  -> (FreeVarName,(STerm Prd Inferred, Loc, TypeScheme Pos)) -> WorkspaceEdit 
generateTranslateEdit (TextDocumentIdentifier uri) (name, (tm,loc,ty)) = 
  let
    newDecl = NamedRep $ PrdCnsDecl () PrdRep Recursive name (Just ty) (createNamesSTerm (compile tm))
    replacement = ppPrint newDecl
    edit = TextEdit {_range=locToRange loc, _newText=replacement}
  in
    WorkspaceEdit { _changes= Just (Map.singleton uri (List [edit]))
                  , _documentChanges=Nothing 
                  , _changeAnnotations=Nothing}
