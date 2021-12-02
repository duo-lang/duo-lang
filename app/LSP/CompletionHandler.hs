module LSP.CompletionHandler (completionHandler) where

import Control.Monad.IO.Class (liftIO)
import Data.Text (Text)
import Language.LSP.Types
import Language.LSP.Server
import System.Log.Logger ( debugM )

import LSP.Definition

completionHandler :: Handlers LSPMonad
completionHandler = requestHandler STextDocumentCompletion $ \req responder -> do
    let (RequestMessage _ _ _ (CompletionParams (TextDocumentIdentifier uri) _ _ _ ctxt)) = req
    liftIO $ debugM "lspserver.completionHandler" ("Received completion request: " <> show uri)
    completionItems <- getCompletionItems ctxt
    responder (Right (InL (List completionItems)))

getCompletionItems :: Maybe CompletionContext -> LSPMonad [CompletionItem]
getCompletionItems _ctx = return [ mkOperatorCompletion "Par" "⅋"
                                 , mkOperatorCompletion "With" "&"
                                 , mkOperatorCompletion "Times" "⊗"
                                 , mkOperatorCompletion "Plus" "⊕"
                                 , mkOperatorCompletion "Fun" "→"
                                 ] 

mkOperatorCompletion :: Text -> Text -> CompletionItem
mkOperatorCompletion name symbol = CompletionItem
                            { _label = name
                            , _kind = Just CiOperator
                            , _tags = Nothing
                            , _detail = Just ("Type operator " <> symbol)
                            , _documentation = Nothing
                            , _deprecated = Just False
                            , _preselect = Nothing
                            , _sortText = Nothing
                            , _filterText = Nothing
                            , _insertText = Just symbol
                            , _insertTextFormat = Nothing
                            , _insertTextMode = Nothing
                            , _textEdit = Nothing
                            , _additionalTextEdits = Nothing
                            , _commitCharacters = Nothing
                            , _command = Nothing
                            , _xdata = Nothing
                            }
