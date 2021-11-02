module LSP.HoverHandler
  ( hoverHandler
  , updateHoverCache
  ) where

import Language.LSP.Types
import Language.LSP.Server
    ( requestHandler, Handlers, getConfig )
import qualified Data.Map as M
import Data.List (sortBy )
import System.Log.Logger ( debugM )
import Pretty.Pretty ( ppPrint )
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import LSP.Definition ( LSPMonad, LSPConfig (MkLSPConfig), HoverMap )
import LSP.MegaparsecToLSP ( locToRange )
import Syntax.Program 
import Syntax.ATerms
import Syntax.STerms hiding (Command)
import qualified Syntax.STerms as STerms
import Syntax.Types 
import TypeTranslation 
import Data.Either (fromRight)
import Data.IORef (readIORef, modifyIORef)
import Data.Text (Text)
import Data.Map (Map)
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

---------------------------------------------------------------------------------
-- Computations on positions and ranges
---------------------------------------------------------------------------------

before :: Position -> Position -> Bool
before (Position line1 column1) (Position line2 column2) = case compare line1 line2 of
  LT -> True
  EQ -> case compare column1 column2 of
    LT -> True
    EQ -> True
    GT -> False
  GT -> False

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


---------------------------------------------------------------------------------
-- Converting Terms to a HoverMap
---------------------------------------------------------------------------------

foo :: (Loc, Typ Pos) -> HoverMap
foo (loc, ty) = M.fromList [(locToRange loc, mkHover $ ppPrint ty)]

atermToHoverMap :: ATerm Inferred -> HoverMap
atermToHoverMap (FVar ext _) = foo ext
atermToHoverMap (BVar ext _) = foo ext
atermToHoverMap (Ctor ext _ args) = M.unions $ [foo ext] <> (atermToHoverMap <$> args)
atermToHoverMap (Dtor ext _ e args) = M.unions $ [foo ext] <> (atermToHoverMap <$> (e:args))
atermToHoverMap (Match ext e cases) = M.unions $ [foo ext] <> (acaseToHoverMap <$> cases) <> [atermToHoverMap e]
atermToHoverMap (Comatch ext cocases) = M.unions $ [foo ext] <> (acaseToHoverMap <$> cocases)

acaseToHoverMap :: ACase Inferred -> HoverMap 
acaseToHoverMap (MkACase _ _ _ tm) = atermToHoverMap tm
---------------------------------------------------------------------------------
-- Converting an environment to a HoverMap
---------------------------------------------------------------------------------

mkHover :: Text -> Hover
mkHover txt = Hover (HoverContents (MarkupContent MkPlainText txt)) Nothing

prdEnvToHoverMap :: Map FreeVarName (STerm Prd Inferred, Loc, TypeScheme Pos) -> HoverMap
prdEnvToHoverMap m =
  let
    ls = M.toList m
    ls' = (\(_,(_,loc,ty)) -> (locToRange loc, mkHover (ppPrint ty))) <$> ls
  in
    M.fromList ls'

cnsEnvToHoverMap :: Map FreeVarName (STerm Cns Inferred, Loc, TypeScheme Neg) -> HoverMap
cnsEnvToHoverMap m = 
  let
    ls = M.toList m
    ls' = (\(_,(_,loc,ty)) -> (locToRange loc,mkHover (ppPrint ty))) <$> ls
  in
    M.fromList ls'

cmdEnvToHoverMap :: Map FreeVarName (STerms.Command Inferred, Loc) -> HoverMap
cmdEnvToHoverMap _ = M.empty

defEnvToHoverMap :: Map FreeVarName (ATerm Inferred, Loc,  TypeScheme Pos) -> HoverMap
defEnvToHoverMap m =
  let
    ls = M.toList m
    f (_,(e,loc,ty)) =
      let
        x :: HoverMap = M.fromList [(locToRange loc, mkHover (ppPrint ty))]
        y :: HoverMap = atermToHoverMap e
      in
        M.union x y
    z = f <$> ls
  in
    M.unions z

declEnvToHoverMap :: Environment -> [(Loc,DataDecl)] -> HoverMap
declEnvToHoverMap env ls =
  let
    ls' = (\(loc,decl) -> (locToRange loc, mkHover (ppPrint (fromRight (error "boom") (translateType env (TyNominal PosRep (data_name decl))))))) <$> ls
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




