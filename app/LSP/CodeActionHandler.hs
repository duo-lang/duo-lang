{-# LANGUAGE TypeOperators #-}
module LSP.CodeActionHandler (codeActionHandler) where

import Language.LSP.Types
import Language.LSP.Server
import Language.LSP.VFS
import qualified Data.Map as M 
import Data.Maybe ( fromMaybe )
import System.Log.Logger ( debugM )
import qualified Data.HashMap.Strict as Map
import Control.Monad.IO.Class ( MonadIO(liftIO) )

import LSP.Definition ( LSPMonad )
import LSP.MegaparsecToLSP ( locToRange )
import Syntax.Program
    ( Declaration(PrdDecl), Environment(prdEnv, defEnv), IsRec(Recursive) )
import Syntax.Types ( Polarity(Pos), TypeScheme )
import Syntax.ATerms
import Syntax.STerms ( createNamesSTerm, STerm )
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
import Eval.Eval ( EvalOrder(..) )
import Translate.Focusing ( focusSTerm, isFocusedSTerm )
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
          responder (Right (generateCodeActions ident env))

generateCodeActions :: TextDocumentIdentifier -> Environment FreeVarName -> List (Command  |? CodeAction)
generateCodeActions ident env = do
  let prds = M.toList $ prdEnv env
  let cbvFocusActions = [ generateFocusCodeAction ident CBV prd | prd@(_,(tm,_,_)) <- prds, not (isFocusedSTerm CBV tm)]
  let cbnFocusActions = [ generateFocusCodeAction ident CBN prd | prd@(_,(tm,_,_)) <- prds, not (isFocusedSTerm CBN tm)]
  let defs = M.toList $ defEnv env
  let translateActions = generateTranslateCodeAction ident <$> defs
  List (cbvFocusActions <> cbnFocusActions <> translateActions)

---------------------------------------------------------------------------------
-- Provide Focus Actions
---------------------------------------------------------------------------------

generateFocusCodeAction :: TextDocumentIdentifier -> EvalOrder -> (FreeVarName, (STerm Prd () FreeVarName, Loc, TypeScheme Pos)) -> Command |? CodeAction
generateFocusCodeAction ident eo arg@(name, _) = InR $ CodeAction { _title = "Focus " <> (case eo of CBV -> "CBV "; CBN -> "CBN ") <> name
                                                                  , _kind = Just CodeActionQuickFix 
                                                                  , _diagnostics = Nothing
                                                                  , _isPreferred = Nothing
                                                                  , _disabled = Nothing
                                                                  , _edit = Just (generateFocusEdit eo ident arg)
                                                                  , _command = Nothing
                                                                  , _xdata = Nothing
                                                                  }

                                      

generateFocusEdit :: EvalOrder -> TextDocumentIdentifier ->  (FreeVarName, (STerm Prd () FreeVarName, Loc, TypeScheme Pos)) -> WorkspaceEdit
generateFocusEdit eo (TextDocumentIdentifier uri) (name,(tm,loc,ty)) =
  let
    newDecl = NamedRep $ PrdDecl Recursive () name (Just ty) (createNamesSTerm (focusSTerm eo tm))
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

generateTranslateCodeAction :: TextDocumentIdentifier -> (FreeVarName,(ATerm () FreeVarName, Loc, TypeScheme Pos)) -> Command |? CodeAction
generateTranslateCodeAction ident arg@(name,_) = InR $ CodeAction { _title = "Translate " <> name
                                                                  , _kind = Just CodeActionQuickFix 
                                                                  , _diagnostics = Nothing
                                                                  , _isPreferred = Nothing
                                                                  , _disabled = Nothing
                                                                  , _edit = Just (generateTranslateEdit ident arg)
                                                                  , _command = Nothing
                                                                  , _xdata = Nothing
                                                                  }

generateTranslateEdit :: TextDocumentIdentifier  -> (FreeVarName,(ATerm () FreeVarName, Loc, TypeScheme Pos)) -> WorkspaceEdit 
generateTranslateEdit (TextDocumentIdentifier uri) (name, (tm,loc,ty)) = 
  let
    newDecl = NamedRep $ PrdDecl Recursive () name (Just ty) (createNamesSTerm (compile tm))
    replacement = ppPrint newDecl
    edit = TextEdit {_range=locToRange loc, _newText=replacement}
  in
    WorkspaceEdit { _changes= Just (Map.singleton uri (List [edit]))
                  , _documentChanges=Nothing 
                  , _changeAnnotations=Nothing}
