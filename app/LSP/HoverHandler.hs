module LSP.HoverHandler
  ( hoverHandler
  , updateHoverCache
  ) where

import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.Either (fromRight)
import Data.IORef (readIORef, modifyIORef)
import Data.List (sortBy )
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Text (Text)
import Language.LSP.Types
import Language.LSP.Server
    ( requestHandler, Handlers, getConfig )
import LSP.Definition ( LSPMonad, LSPConfig (MkLSPConfig), HoverMap, sendInfo )
import LSP.MegaparsecToLSP
import System.Log.Logger ( debugM )

import Driver.Environment
import Pretty.Pretty ( ppPrint )
import Pretty.Common ()
import Syntax.Common
import Syntax.AST.Terms hiding (Command)
import Syntax.AST.Terms qualified as Terms
import Syntax.AST.Types
import TypeTranslation
import Utils (Loc)

---------------------------------------------------------------------------------
-- Handle Type on Hover
---------------------------------------------------------------------------------

hoverHandler :: Handlers LSPMonad
hoverHandler = requestHandler STextDocumentHover $ \req responder ->  do
  let (RequestMessage _ _ _ (HoverParams (TextDocumentIdentifier uri) pos _)) = req
  liftIO $ debugM "lspserver.hoverHandler" ("Received hover request: " <> show uri <> " at: " <> show pos)
  MkLSPConfig ref <- getConfig
  cache <- liftIO $ readIORef ref
  case M.lookup uri cache of
    Nothing -> do
      sendInfo ("Hover Cache not initialized for: " <> T.pack (show uri))
      responder (Right Nothing)
    Just cache -> responder (Right (lookupInHoverMap pos cache))


updateHoverCache :: Uri -> Environment Inferred -> LSPMonad ()
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
-- Generating HoverMaps
---------------------------------------------------------------------------------

-- | A class for generating HoverMaps
class ToHoverMap a where
  toHoverMap :: a -> HoverMap

mkHover :: Text -> Range ->  Hover
mkHover txt rng = Hover (HoverContents (MarkupContent MkPlainText txt)) (Just rng)

mkHoverMap :: Loc -> Text -> HoverMap
mkHoverMap loc msg = M.fromList [(locToRange loc, mkHover msg (locToRange loc))]

---------------------------------------------------------------------------------
-- Converting Terms to a HoverMap
---------------------------------------------------------------------------------

instance ToHoverMap (TermCase Inferred) where
  toHoverMap (MkTermCase _ _ _ tm) = toHoverMap tm

instance ToHoverMap (TermCaseI Inferred) where
  toHoverMap (MkTermCaseI _ _ _ tm) = toHoverMap tm

instance ToHoverMap (CmdCase Inferred) where
  toHoverMap (MkCmdCase {cmdcase_cmd}) = toHoverMap cmdcase_cmd


boundVarToHoverMap :: Loc -> Typ pol -> HoverMap
boundVarToHoverMap loc ty = mkHoverMap loc msg
  where
    msg :: Text
    msg = "Bound variable\nType: " <> (ppPrint ty)

freeVarToHoverMap :: Loc -> Typ pol -> HoverMap
freeVarToHoverMap loc ty = mkHoverMap loc msg
  where
    msg :: Text
    msg = "Free variable\nType: " <> (ppPrint ty)

xtorToHoverMap :: Loc -> PrdCnsRep pc -> Typ pol -> NominalStructural -> HoverMap
xtorToHoverMap loc pc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = case pc of
      PrdRep -> (ppPrint ns) <> " constructor (Right-Intro)\nType: " <> (ppPrint ty)
      CnsRep -> (ppPrint ns) <> " destructor (Left-Intro)\nType: "  <> (ppPrint ty)

xcaseToHoverMap :: Loc -> PrdCnsRep pc -> Typ pol -> NominalStructural -> HoverMap
xcaseToHoverMap loc pc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = case pc of
      PrdRep -> (ppPrint ns) <> " cocase (Right-Intro)\nType: " <> (ppPrint ty)
      CnsRep -> (ppPrint ns) <> " case (Left-Intro)\nType: " <> (ppPrint ty)

muAbsToHoverMap :: Loc -> PrdCnsRep pc -> Typ pol -> HoverMap
muAbsToHoverMap loc pc ty = mkHoverMap loc msg
  where
    msg :: Text
    msg = case pc of
      PrdRep -> "μ-Abstraction\nType: " <> (ppPrint ty)
      CnsRep -> "~μ-Abstraction\nType: " <> (ppPrint ty)

dtorToHoverMap :: Loc -> Typ pol -> NominalStructural -> HoverMap
dtorToHoverMap loc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = (ppPrint ns) <> " destructor application (Right-Elim)\nType: " <> (ppPrint ty)

caseToHoverMap :: Loc -> Typ pol -> NominalStructural -> HoverMap
caseToHoverMap loc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = (ppPrint ns) <> " case-of (Right-Elim)\nType: " <> (ppPrint ty)

cocaseToHoverMap :: Loc -> Typ pol -> NominalStructural -> HoverMap
cocaseToHoverMap loc ty ns = mkHoverMap loc msg
  where
    msg :: Text
    msg = (ppPrint ns) <> " cocase (Right-Intro)\nType: " <> (ppPrint ty)

instance ToHoverMap (Term pc Inferred) where
  toHoverMap (BoundVar (loc, ty) _ _)           = boundVarToHoverMap loc ty
  toHoverMap (FreeVar (loc, ty) _ _)            = freeVarToHoverMap loc ty
  toHoverMap (Xtor (loc, ty) pc ns _ args)      = M.unions [xtorToHoverMap loc pc ty ns, toHoverMap args]
  toHoverMap (XMatch (loc,ty) pc ns cases)      = M.unions $ xcaseToHoverMap loc pc ty ns : (toHoverMap <$> cases)
  toHoverMap (MuAbs (loc,ty) pc _ cmd)          = M.unions [muAbsToHoverMap loc pc ty, toHoverMap cmd]
  toHoverMap (Dtor (loc,ty) ns _ e (s1,_,s2))   = M.unions $ [dtorToHoverMap loc ty ns] <> (toHoverMap <$> (PrdTerm e:(s1 ++ s2)))
  toHoverMap (Case (loc,ty) ns e cases)         = M.unions $ [caseToHoverMap loc ty ns] <> (toHoverMap <$> cases) <> [toHoverMap e]
  toHoverMap (Cocase (loc,ty) ns cocases)       = M.unions $ [cocaseToHoverMap loc ty ns] <> (toHoverMap <$> cocases)
  toHoverMap (PrimLitI64 (loc,ty) _)            = mkHoverMap loc ("Raw #I64 Literal\nType: " <> ppPrint ty)
  toHoverMap (PrimLitF64 (loc,ty) _)            = mkHoverMap loc ("Raw #F64 Literal\nType: " <> ppPrint ty)

instance ToHoverMap (PrdCnsTerm Inferred) where
  toHoverMap (PrdTerm tm) = toHoverMap tm
  toHoverMap (CnsTerm tm) = toHoverMap tm

applyToHoverMap :: Range -> Maybe MonoKind -> HoverMap
applyToHoverMap rng Nothing   = M.fromList [(rng, mkHover "Kind not inferred" rng)]
applyToHoverMap rng (Just cc) = M.fromList [(rng, mkHover (ppPrint cc) rng)]

instance ToHoverMap (Terms.Command Inferred) where
  toHoverMap (Apply loc kind prd cns) = M.unions [toHoverMap prd, toHoverMap cns, applyToHoverMap (locToRange loc) kind]
  toHoverMap (Print _ prd cmd)        = M.unions [toHoverMap prd, toHoverMap cmd]
  toHoverMap (Read _ cns)             = toHoverMap cns
  toHoverMap (Call _ _)               = M.empty
  toHoverMap (Done _)                 = M.empty
  toHoverMap PrimOp {}                = M.empty

instance ToHoverMap (Substitution Inferred) where
  toHoverMap subst = M.unions (toHoverMap <$> subst)

---------------------------------------------------------------------------------
-- Converting an environment to a HoverMap
---------------------------------------------------------------------------------

prdEnvToHoverMap :: Map FreeVarName (Term Prd Inferred, Loc, TypeScheme Pos) -> HoverMap
prdEnvToHoverMap = M.unions . fmap f . M.toList
  where
    f (_,(e,loc,ty)) =
      let
        outerHover = M.fromList [(locToRange loc, mkHover (ppPrint ty) (locToRange loc))]
        termHover = toHoverMap e
      in
        M.union outerHover termHover

cnsEnvToHoverMap :: Map FreeVarName (Term Cns Inferred, Loc, TypeScheme Neg) -> HoverMap
cnsEnvToHoverMap = M.unions . fmap f . M.toList
  where
    f (_,(e,loc,ty)) =
      let
        outerHover = M.fromList [(locToRange loc, mkHover (ppPrint ty) (locToRange loc))]
        termHover = toHoverMap e
      in
        M.union outerHover termHover


cmdEnvToHoverMap :: Map FreeVarName (Terms.Command Inferred, Loc) -> HoverMap
cmdEnvToHoverMap = M.unions. fmap f . M.toList
  where
    f (_, (cmd,_)) = toHoverMap cmd

declEnvToHoverMap :: Environment Inferred -> [(Loc,DataDecl)] -> HoverMap
declEnvToHoverMap env ls =
  let
    ls' = (\(loc,decl) -> (locToRange loc, mkHover (printTranslation decl) (locToRange loc))) <$> ls
  in
    M.fromList ls'
  where
    printTranslation :: DataDecl -> Text
    printTranslation NominalDecl{..} = case data_polarity of
      Data   -> ppPrint $ fromRight (error "boom") $ translateTypeUpper env (TyNominal NegRep Nothing data_name [] [])
      Codata -> ppPrint $ fromRight (error "boom") $ translateTypeLower env (TyNominal PosRep Nothing data_name [] [])

lookupHoverEnv :: Environment Inferred -> HoverMap
lookupHoverEnv env@MkEnvironment { prdEnv, cnsEnv, cmdEnv, declEnv } =
  M.unions [ prdEnvToHoverMap prdEnv
           , cnsEnvToHoverMap cnsEnv
           , cmdEnvToHoverMap cmdEnv
           , declEnvToHoverMap env declEnv
           ]




