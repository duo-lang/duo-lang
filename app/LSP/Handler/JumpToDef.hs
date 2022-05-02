module LSP.Handler.JumpToDef ( jumpToDefHandler ) where

import Data.Map (Map)
import Data.Map qualified as M
import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Language.LSP.Types
import Language.LSP.Server
import Language.LSP.VFS
import LSP.Definition
import LSP.MegaparsecToLSP
import System.Log.Logger
import Syntax.RST.Types qualified as RST
import Syntax.RST.Program qualified as RST
import Translate.ForgetTypes ( forgetTypesProgram )
import Syntax.Common
import Data.Maybe ( fromMaybe )

import Driver.Definition ( defaultDriverState )
import Driver.Driver ( inferProgramIO )
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Syntax.RST.Types (TypeScheme(ts_monotype))

jumpToDefHandler :: Handlers LSPMonad
jumpToDefHandler = requestHandler STextDocumentDefinition $ \req responder -> do
    let (RequestMessage _ _ _ (DefinitionParams (TextDocumentIdentifier uri) pos _ _)) = req
    liftIO $ debugM "lspserver.JumpToDefHandler" ("Received definition request: " <> show uri <> " at: " <> show pos)
    mfile <- getVirtualFile (toNormalizedUri uri)
    let vfile :: VirtualFile = maybe (error "Virtual File not present!") id mfile
    let file = virtualFileText vfile
    let fp = fromMaybe "fail" (uriToFilePath uri)
    let decls = runFileParser fp programP file
    case decls of
      Left _err -> do
        responder (Left (ResponseError { _code = InvalidRequest, _message = "", _xdata = Nothing}))
      Right decls -> do
        res <- liftIO $ inferProgramIO defaultDriverState (MkModuleName (getUri uri)) decls
        case res of
          Left _err -> do
            responder (Left (ResponseError { _code = InvalidRequest, _message = "", _xdata = Nothing}))
          Right (_,prog) -> do
            responder (generateJumpToDef pos (forgetTypesProgram prog))
    

generateJumpToDef :: Position -> RST.Program -> Either ResponseError (Location |? b)
generateJumpToDef pos prog = do
    let jumpMap = toJumpMap prog
    case lookupInRangeMap pos jumpMap of
        Nothing -> (Left (ResponseError { _code = InvalidRequest, _message = "", _xdata = Nothing }))
        Just loc -> Right (InL loc)


class ToLocation a where
  toLocation :: a -> Location

class ToJumpMap a where
    toJumpMap :: a -> Map Range Location

instance ToJumpMap (RST.VariantType pol) where
  toJumpMap (RST.CovariantType ty) = toJumpMap ty
  toJumpMap (RST.ContravariantType ty) = toJumpMap ty

instance ToJumpMap (RST.PrdCnsType pol) where
  toJumpMap (RST.PrdCnsType _ ty) = toJumpMap ty

instance ToJumpMap (RST.Typ pol) where
  toJumpMap RST.TyVar {} =
    M.empty
  toJumpMap (RST.TyData loc _ (Just tn) xtors) =
    M.unions (M.fromList [(locToRange loc, toLocation tn)] : (toJumpMap <$> xtors))
  toJumpMap (RST.TyData _ _ Nothing xtors) =
    M.unions (toJumpMap <$> xtors)
  toJumpMap (RST.TyCodata loc _ (Just tn) xtors) =
    M.unions (M.fromList [(locToRange loc, toLocation tn)] : (toJumpMap <$> xtors))
  toJumpMap (RST.TyCodata _ _ Nothing xtors) =
    M.unions (toJumpMap <$> xtors)
  toJumpMap (RST.TyNominal loc _ _ rn args) =
    M.unions (M.fromList [(locToRange loc, toLocation rn)] : (toJumpMap <$> args))
  toJumpMap (RST.TySyn loc _ rn _) =
    M.fromList [(locToRange loc, toLocation rn)]
  toJumpMap RST.TyBot {} = M.empty
  toJumpMap RST.TyTop {} = M.empty
  toJumpMap (RST.TyUnion _ _ ty1 ty2) =
    M.union (toJumpMap ty1) (toJumpMap ty2)
  toJumpMap (RST.TyInter _ _ ty1 ty2) =
    M.union (toJumpMap ty1) (toJumpMap ty2)
  toJumpMap (RST.TyRec _ _ _ ty) =
    toJumpMap ty
  toJumpMap RST.TyPrim {} = M.empty

instance ToJumpMap (RST.XtorSig pol) where
  toJumpMap (RST.MkXtorSig _ ctx) = M.unions (toJumpMap <$> ctx)

instance ToJumpMap (RST.TypeScheme pol) where
  toJumpMap RST.TypeScheme { ts_monotype } =
    toJumpMap ts_monotype

instance ToJumpMap RST.Program where
  toJumpMap prog = M.unions (toJumpMap <$> prog)

instance ToJumpMap RST.Declaration where
  toJumpMap (RST.PrdCnsDecl _ _ _ _ _ Nothing _) = M.empty
  toJumpMap (RST.PrdCnsDecl _ _ _ _ _ (Just tys) _) = toJumpMap tys
  toJumpMap RST.CmdDecl {} = M.empty
  toJumpMap RST.DataDecl {} = M.empty
  toJumpMap RST.XtorDecl {} = M.empty
  toJumpMap RST.ImportDecl {} = M.empty
  toJumpMap RST.SetDecl {} = M.empty
  toJumpMap (RST.TyOpDecl loc _ _ _ _ rnTn) = M.fromList [(locToRange loc, toLocation rnTn)]
  toJumpMap RST.TySynDecl {} = M.empty

instance ToLocation RnTypeName where
  toLocation MkRnTypeName { rnTnLoc, rnTnModule } =
    let rng = locToRange rnTnLoc
    in  Location { _uri = Uri $ "" <> unModuleName rnTnModule
                 , _range = rng
                 }