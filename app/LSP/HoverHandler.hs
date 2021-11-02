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

-- Define an ordering on Positions
positionOrd :: Position -> Position -> Ordering
positionOrd (Position line1 column1) (Position line2 column2) =
  case compare line1 line2 of
    LT -> LT
    EQ -> compare column1 column2
    GT -> GT

-- | Check whether the first position comes textually before the second position.
before :: Position -> Position -> Bool
before pos1 pos2 = case positionOrd pos1 pos2 of
  LT -> True
  EQ -> True
  GT -> False

-- | Check whether a given position lies within a given range
inRange :: Position -> Range -> Bool
inRange pos (Range startPos endPos) = before startPos pos && before pos endPos

-- | Order ranges according to their starting position
rangeOrd :: Range -> Range -> Ordering 
rangeOrd (Range start1 _) (Range start2 _) = positionOrd start1 start2

lookupInHoverMap :: Position -> HoverMap -> Maybe Hover
lookupInHoverMap pos map =
  let
    withinRange :: [(Range, Hover)] = M.toList $ M.filterWithKey (\k _ -> inRange pos k) map
    -- | Sort them so that the range starting with the latest(!) starting position
    -- comes first.
    withinRangeOrdered = sortBy (\(r1,_) (r2,_) -> rangeOrd r2 r1) withinRange
  in
    case withinRangeOrdered of
      [] -> Nothing 
      ((_,ho):_) -> Just ho


---------------------------------------------------------------------------------
-- Converting Terms to a HoverMap
---------------------------------------------------------------------------------

foo :: (Loc, Typ Pos) -> HoverMap
foo (loc, ty) = M.fromList [(locToRange loc, mkHover $ ppPrint ty)]

atermToHoverMap :: ATerm Inferred -> HoverMap
atermToHoverMap (FVar ext _)          = foo ext
atermToHoverMap (BVar ext _)          = foo ext
atermToHoverMap (Ctor ext _ args)     = M.unions $ [foo ext] <> (atermToHoverMap <$> args)
atermToHoverMap (Dtor ext _ e args)   = M.unions $ [foo ext] <> (atermToHoverMap <$> (e:args))
atermToHoverMap (Match ext e cases)   = M.unions $ [foo ext] <> (acaseToHoverMap <$> cases) <> [atermToHoverMap e]
atermToHoverMap (Comatch ext cocases) = M.unions $ [foo ext] <> (acaseToHoverMap <$> cocases)

acaseToHoverMap :: ACase Inferred -> HoverMap 
acaseToHoverMap (MkACase _ _ _ tm) = atermToHoverMap tm

bar :: (Loc, SomeType) -> HoverMap
bar (loc, PosType ty) = M.fromList [(locToRange loc, mkHover $ ppPrint ty)]
bar (loc, NegType ty) = M.fromList [(locToRange loc, mkHover $ ppPrint ty)]


stermToHoverMap :: STerm pc Inferred -> HoverMap 
stermToHoverMap (BoundVar ext _ _)      = bar ext
stermToHoverMap (FreeVar ext _ _)       = bar ext
stermToHoverMap (XtorCall ext _ _ args) = M.unions [bar ext, xtorArgsToHoverMap args]
stermToHoverMap (XMatch ext _ _ cases)  = M.unions $ bar ext : (scaseToHoverMap <$> cases)
stermToHoverMap (MuAbs ext _ _ cmd)     = M.unions [bar ext, commandToHoverMap cmd]

commandToHoverMap :: STerms.Command Inferred -> HoverMap
commandToHoverMap (Apply _ prd cns) = M.unions [stermToHoverMap prd, stermToHoverMap cns]
commandToHoverMap (Print _ prd)     = stermToHoverMap prd
commandToHoverMap (Done _)          = M.empty 

xtorArgsToHoverMap :: XtorArgs Inferred -> HoverMap
xtorArgsToHoverMap (MkXtorArgs prdArgs cnsArgs) =
  M.unions $ (stermToHoverMap <$> prdArgs) <> (stermToHoverMap <$> cnsArgs)

scaseToHoverMap :: SCase Inferred -> HoverMap
scaseToHoverMap (MkSCase {scase_cmd}) = commandToHoverMap scase_cmd


---------------------------------------------------------------------------------
-- Converting an environment to a HoverMap
---------------------------------------------------------------------------------

mkHover :: Text -> Hover
mkHover txt = Hover (HoverContents (MarkupContent MkPlainText txt)) Nothing

prdEnvToHoverMap :: Map FreeVarName (STerm Prd Inferred, Loc, TypeScheme Pos) -> HoverMap
prdEnvToHoverMap = M.unions . fmap f . M.toList
  where
    f (_,(e,loc,ty)) = 
      let
        outerHover = M.fromList [(locToRange loc, mkHover (ppPrint ty))]
        termHover = stermToHoverMap e
      in
        M.union outerHover termHover

cnsEnvToHoverMap :: Map FreeVarName (STerm Cns Inferred, Loc, TypeScheme Neg) -> HoverMap
cnsEnvToHoverMap = M.unions . fmap f . M.toList
  where
    f (_,(e,loc,ty)) =
      let
        outerHover = M.fromList [(locToRange loc, mkHover (ppPrint ty))]
        termHover = stermToHoverMap e 
      in
        M.union outerHover termHover
  

cmdEnvToHoverMap :: Map FreeVarName (STerms.Command Inferred, Loc) -> HoverMap
cmdEnvToHoverMap = M.unions. fmap f . M.toList
  where
    f (_, (cmd,_)) = commandToHoverMap cmd

defEnvToHoverMap :: Map FreeVarName (ATerm Inferred, Loc,  TypeScheme Pos) -> HoverMap
defEnvToHoverMap = M.unions . fmap f . M.toList
  where
    f (_,(e,loc,ty)) =
      let
        outerHover = M.fromList [(locToRange loc, mkHover (ppPrint ty))]
        termHover  = atermToHoverMap e
      in
        M.union outerHover termHover


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




