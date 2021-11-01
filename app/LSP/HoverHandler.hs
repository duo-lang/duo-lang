module LSP.HoverHandler
  ( hoverHandler
  , updateHoverCache
  ) where

import Language.LSP.Types
import Language.LSP.Server
    ( requestHandler, Handlers, getConfig )
import qualified Data.Map as M
import Data.List ( find, sortBy )
import System.Log.Logger ( debugM )
import Pretty.Pretty ( ppPrint )
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import LSP.Definition ( LSPMonad, LSPConfig (MkLSPConfig), HoverMap )
import LSP.MegaparsecToLSP ( lookupPos )
import Syntax.Program ( Environment(defEnv, prdEnv, cnsEnv, declEnv) )
import Syntax.Types ( Typ(TyNominal), PolarityRep (PosRep), DataDecl (data_name) )
import TypeTranslation ( translateType )
import Syntax.Types (Polarity(Pos))
import Data.Either (fromRight)
import Data.IORef (readIORef, modifyIORef)
import Data.Text.Internal.Lazy (Text)
import Data.Map (Map)

---------------------------------------------------------------------------------
-- Handle Type on Hover
---------------------------------------------------------------------------------

hoverHandler :: Handlers LSPMonad
hoverHandler = requestHandler STextDocumentHover $ \req responder ->  do
  let (RequestMessage _ _ _ (HoverParams (TextDocumentIdentifier uri) pos _workDone)) = req
  liftIO $ debugM "lspserver.hoverHandler" ("Received hover request: " <> show uri)
  MkLSPConfig ref <- getConfig 
  cache <- liftIO $ readIORef ref
  case M.lookup uri cache of
    Nothing -> responder (Right Nothing)
    Just cache -> responder (Right (cache pos))
 

updateHoverCache :: Uri -> Environment -> LSPMonad ()
updateHoverCache uri env = do
  MkLSPConfig ref <- getConfig
  liftIO $ modifyIORef ref (M.insert uri (lookupHoverEnv env))



before :: Position -> Position -> Bool
before = undefined

inRange :: Position -> Range -> Bool
inRange pos (Range startPos endPos) = before startPos pos && before pos endPos


positionOrd :: Position -> Position -> Ordering
positionOrd (Position line1 column1) (Position line2 column2) = case compare line1 line2 of
  LT -> LT
  EQ -> compare column1 column2
  GT -> GT

rangeOrd :: Range -> Range -> Ordering 
rangeOrd (Range start1 _) (Range start2 _) = positionOrd start1 start2

lookupInHoverMap :: Position -> HoverMap -> Maybe Hover
lookupInHoverMap pos map =
  let
    x = M.filterWithKey (\k _ -> inRange pos k) map
    y = M.toList x
    z = sortBy (\(k,_) (k',_) -> rangeOrd k k') y
  in
    case z of
      [] -> Nothing 
      ((_,ho):_) -> Just ho


lookupHoverEnv :: Environment -> Position -> Maybe Hover
lookupHoverEnv env pos =
  let
    defs = M.toList (defEnv env)
    defres = find (\(_,(_,loc,_)) -> lookupPos pos loc) defs
    prds = M.toList (prdEnv env)
    prdres = find (\(_,(_,loc,_)) -> lookupPos pos loc) prds
    cnss = M.toList (cnsEnv env)
    cnsres = find (\(_,(_,loc,_)) -> lookupPos pos loc) cnss
    typs = find (\(loc,_) -> lookupPos pos loc) (declEnv env)
  in
    case defres of
      Just (_,(_,_,ty)) -> Just (Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)
      Nothing -> case prdres of
        Just (_,(_,_,ty)) -> Just (Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)
        Nothing -> case cnsres of
          Just (_,(_,_,ty)) -> Just (Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)
          Nothing -> case typs of
            Just (_,decl) ->
              let ty :: Typ Pos = fromRight (error "boom") (translateType env (TyNominal PosRep (data_name decl)))
              in Just (Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)
            Nothing -> Nothing



