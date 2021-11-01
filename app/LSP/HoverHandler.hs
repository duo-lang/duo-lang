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
import LSP.MegaparsecToLSP ( lookupPos, locToRange )
import Syntax.Program 
import Syntax.ATerms
import Syntax.STerms hiding (Command)
import qualified Syntax.STerms as STerms
import Syntax.Types 
import TypeTranslation 
import Syntax.Types 
import Data.Either (fromRight)
import Data.IORef (readIORef, modifyIORef)
import Data.Text.Internal.Lazy (Text)
import Data.Map (Map)
import GHC.IO.Exception (ArrayException(UndefinedElement))
import Utils (Loc)

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
    Just cache -> responder (Right (lookupInHoverMap pos cache))
 

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




prdEnvToHoverMap :: Map FreeVarName (STerm Prd Compiled, Loc, TypeScheme Pos) -> HoverMap
prdEnvToHoverMap m =
  let
    ls = M.toList m
    ls' = (\(_,(_,loc,ty)) -> (locToRange loc,Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)) <$> ls
  in
    M.fromList ls'

cnsEnvToHoverMap :: Map FreeVarName (STerm Cns Compiled, Loc, TypeScheme Neg) -> HoverMap
cnsEnvToHoverMap m = 
  let
    ls = M.toList m
    ls' = (\(_,(_,loc,ty)) -> (locToRange loc,Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)) <$> ls
  in
    M.fromList ls'

cmdEnvToHoverMap :: Map FreeVarName (STerms.Command Compiled, Loc) -> HoverMap
cmdEnvToHoverMap _ = M.empty

defEnvToHoverMap :: Map FreeVarName (ATerm Compiled, Loc,  TypeScheme Pos) -> HoverMap
defEnvToHoverMap m =
  let
    ls = M.toList m
    ls' = (\(_,(_,loc,ty)) -> (locToRange loc, Hover (HoverContents (MarkupContent MkPlainText (ppPrint ty))) Nothing)) <$> ls
  in
    M.fromList ls'

declEnvToHoverMap :: Environment -> [(Loc,DataDecl)] -> HoverMap
declEnvToHoverMap env ls =
  let
    ls' = (\(loc,decl) -> (locToRange loc, Hover (HoverContents (MarkupContent MkPlainText (ppPrint (fromRight (error "boom") (translateType env (TyNominal PosRep (data_name decl))))))) Nothing)) <$> ls
  in
    M.fromList ls'

lookupHoverEnv :: Environment -> HoverMap
lookupHoverEnv env@Environment { prdEnv, cnsEnv, cmdEnv, defEnv, declEnv } = 
  M.unions [ prdEnvToHoverMap prdEnv
           , cnsEnvToHoverMap cnsEnv
           , cmdEnvToHoverMap cmdEnv
           , defEnvToHoverMap defEnv
           , declEnvToHoverMap env declEnv
           ]




