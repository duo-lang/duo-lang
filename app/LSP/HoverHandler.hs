module LSP.HoverHandler
  ( hoverHandler
  , updateHoverCache
  ) where

import Language.LSP.Types
import Language.LSP.Server
    ( requestHandler, Handlers, getConfig )
import Data.Map qualified as M
import Data.List (sortBy )
import System.Log.Logger ( debugM )
import Pretty.Pretty ( ppPrint )
import Control.Monad.IO.Class ( MonadIO(liftIO) )

import LSP.Definition ( LSPMonad, LSPConfig (MkLSPConfig), HoverMap )
import LSP.MegaparsecToLSP


import Syntax.Program 
import Syntax.CommonTerm
import Syntax.Terms hiding (Command)
import Syntax.Terms qualified as Terms
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
foo (loc, ty) = M.fromList [(locToRange loc, mkHover (ppPrint ty) (locToRange loc))]



acaseToHoverMap :: ACase Inferred -> HoverMap 
acaseToHoverMap (MkACase _ _ _ tm) = stermToHoverMap tm

bar :: (Loc, Typ pol) -> HoverMap
bar (loc, ty) = M.fromList [(locToRange loc, mkHover (ppPrint ty) (locToRange loc))]

stermToHoverMap :: Term pc Inferred -> HoverMap 
stermToHoverMap (BoundVar ext PrdRep _)      = bar ext
stermToHoverMap (BoundVar ext CnsRep _)      = bar ext
stermToHoverMap (FreeVar ext PrdRep _)       = bar ext
stermToHoverMap (FreeVar ext CnsRep _)       = bar ext
stermToHoverMap (XtorCall ext PrdRep _ args) = M.unions [bar ext, xtorArgsToHoverMap args]
stermToHoverMap (XtorCall ext CnsRep _ args) = M.unions [bar ext, xtorArgsToHoverMap args]
stermToHoverMap (XMatch ext PrdRep _ cases)  = M.unions $ bar ext : (scaseToHoverMap <$> cases)
stermToHoverMap (XMatch ext CnsRep _ cases)  = M.unions $ bar ext : (scaseToHoverMap <$> cases)
stermToHoverMap (MuAbs ext PrdRep _ cmd)     = M.unions [bar ext, commandToHoverMap cmd]
stermToHoverMap (MuAbs ext CnsRep _ cmd)     = M.unions [bar ext, commandToHoverMap cmd]
stermToHoverMap (Dtor ext _ e args)   = M.unions $ [foo ext] <> (stermToHoverMap <$> (e:args))
stermToHoverMap (Match ext e cases)   = M.unions $ [foo ext] <> (acaseToHoverMap <$> cases) <> [stermToHoverMap e]
stermToHoverMap (Comatch ext cocases) = M.unions $ [foo ext] <> (acaseToHoverMap <$> cocases)

commandToHoverMap :: Terms.Command Inferred -> HoverMap
commandToHoverMap (Apply _ prd cns) = M.unions [stermToHoverMap prd, stermToHoverMap cns]
commandToHoverMap (Print _ prd)     = stermToHoverMap prd
commandToHoverMap (Done _)          = M.empty 

xtorArgsToHoverMap :: Substitution Inferred -> HoverMap
xtorArgsToHoverMap (MkSubst prdArgs cnsArgs) =
  M.unions $ (stermToHoverMap <$> prdArgs) <> (stermToHoverMap <$> cnsArgs)

scaseToHoverMap :: SCase Inferred -> HoverMap
scaseToHoverMap (MkSCase {scase_cmd}) = commandToHoverMap scase_cmd


---------------------------------------------------------------------------------
-- Converting an environment to a HoverMap
---------------------------------------------------------------------------------

mkHover :: Text -> Range ->  Hover
mkHover txt rng = Hover (HoverContents (MarkupContent MkPlainText txt)) (Just rng)

prdEnvToHoverMap :: Map FreeVarName (Term Prd Inferred, Loc, TypeScheme Pos) -> HoverMap
prdEnvToHoverMap = M.unions . fmap f . M.toList
  where
    f (_,(e,loc,ty)) = 
      let
        outerHover = M.fromList [(locToRange loc, mkHover (ppPrint ty) (locToRange loc))]
        termHover = stermToHoverMap e
      in
        M.union outerHover termHover

cnsEnvToHoverMap :: Map FreeVarName (Term Cns Inferred, Loc, TypeScheme Neg) -> HoverMap
cnsEnvToHoverMap = M.unions . fmap f . M.toList
  where
    f (_,(e,loc,ty)) =
      let
        outerHover = M.fromList [(locToRange loc, mkHover (ppPrint ty) (locToRange loc))]
        termHover = stermToHoverMap e 
      in
        M.union outerHover termHover
  

cmdEnvToHoverMap :: Map FreeVarName (Terms.Command Inferred, Loc) -> HoverMap
cmdEnvToHoverMap = M.unions. fmap f . M.toList
  where
    f (_, (cmd,_)) = commandToHoverMap cmd

declEnvToHoverMap :: Environment -> [(Loc,DataDecl)] -> HoverMap
declEnvToHoverMap env ls =
  let
    ls' = (\(loc,decl) -> (locToRange loc, mkHover (printTranslation decl) (locToRange loc))) <$> ls
  in
    M.fromList ls'
  where
    printTranslation :: DataDecl -> Text
    printTranslation NominalDecl{..} = case data_polarity of
      Data   -> ppPrint $ fromRight (error "boom") $ translateTypeUpper env (TyNominal NegRep data_name)
      Codata -> ppPrint $ fromRight (error "boom") $ translateTypeLower env (TyNominal PosRep data_name)

lookupHoverEnv :: Environment -> HoverMap
lookupHoverEnv env@Environment { prdEnv, cnsEnv, cmdEnv, declEnv } = 
  M.unions [ prdEnvToHoverMap prdEnv
           , cnsEnvToHoverMap cnsEnv
           , cmdEnvToHoverMap cmdEnv
           , declEnvToHoverMap env declEnv
           ]




