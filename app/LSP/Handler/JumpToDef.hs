module LSP.Handler.JumpToDef ( jumpToDefHandler ) where

import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.Map (Map)
import Data.Map qualified as M
import Data.Maybe ( fromMaybe )
import Data.Text qualified as T
import Language.LSP.Types
    ( Uri(Uri),
      Range,
      SMethod(STextDocumentDefinition),
      RequestMessage(RequestMessage),
      ResponseError(..),
      TextDocumentIdentifier(TextDocumentIdentifier),
      toNormalizedUri,
      type (|?)(InL),
      uriToFilePath,
      DefinitionParams(DefinitionParams),
      Location(..),
      Position,
      ErrorCode(InvalidRequest) )
import Language.LSP.Server
    ( getVirtualFile, requestHandler, Handlers )
import Language.LSP.VFS ( VirtualFile, virtualFileText )
import System.Log.Logger ( debugM )

import Driver.Definition ( defaultDriverState )
import Driver.Driver ( inferProgramIO )
import LSP.Definition ( LSPMonad )
import LSP.MegaparsecToLSP ( locToRange, lookupInRangeMap )
import Parser.Definition ( runFileParser )
import Parser.Program ( moduleP )
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Names
import Syntax.RST.Types qualified as RST
import Syntax.RST.Program qualified as RST
import Translate.Embed

jumpToDefHandler :: Handlers LSPMonad
jumpToDefHandler = requestHandler STextDocumentDefinition $ \req responder -> do
    let (RequestMessage _ _ _ (DefinitionParams (TextDocumentIdentifier uri) pos _ _)) = req
    liftIO $ debugM "lspserver.JumpToDefHandler" ("Received definition request: " <> show uri <> " at: " <> show pos)
    mfile <- getVirtualFile (toNormalizedUri uri)
    let vfile :: VirtualFile = fromMaybe (error "Virtual File not present!") mfile
    let file = virtualFileText vfile
    let fp = fromMaybe "fail" (uriToFilePath uri)
    let decls = runFileParser fp (moduleP fp) file
    case decls of
      Left _err -> do
        responder (Left (ResponseError { _code = InvalidRequest, _message = "", _xdata = Nothing}))
      Right decls -> do
        (res, _warnings) <- liftIO $ inferProgramIO defaultDriverState decls
        case res of
          Left _err -> do
            responder (Left (ResponseError { _code = InvalidRequest, _message = "", _xdata = Nothing}))
          Right (_,prog) -> do
            responder (generateJumpToDef pos (embedCoreModule (embedTSTModule prog)))


generateJumpToDef :: Position -> RST.Module -> Either ResponseError (Location |? b)
generateJumpToDef pos prog = do
    let jumpMap = toJumpMap prog
    case lookupInRangeMap pos jumpMap of
        Nothing -> Left (ResponseError { _code = InvalidRequest, _message = "", _xdata = Nothing })
        Just loc -> Right (InL loc)

---------------------------------------------------------------------------------
-- Typeclasses for generating JumpMaps
---------------------------------------------------------------------------------

class ToLocation a where
  toLocation :: a -> Location

class ToJumpMap a where
  toJumpMap :: a -> Map Range Location

---------------------------------------------------------------------------------
-- Converting Terms to a JumpMap
---------------------------------------------------------------------------------

instance ToJumpMap RST.PrdCnsTerm where
  toJumpMap (RST.PrdTerm tm) = toJumpMap tm
  toJumpMap (RST.CnsTerm tm) = toJumpMap tm

instance ToJumpMap RST.Substitution where
  toJumpMap subst = M.unions (toJumpMap <$> subst)

instance ToJumpMap (RST.SubstitutionI pc) where
  toJumpMap (subst1,_,subst2) =
    M.unions ((toJumpMap <$> subst1) ++ (toJumpMap <$> subst2))

instance ToJumpMap RST.CmdCase where
  toJumpMap RST.MkCmdCase { cmdcase_cmd } =
    toJumpMap cmdcase_cmd

instance ToJumpMap RST.InstanceCase where
  toJumpMap RST.MkInstanceCase { instancecase_cmd } =
    toJumpMap instancecase_cmd

instance ToJumpMap (RST.TermCase pc) where
  toJumpMap RST.MkTermCase { tmcase_term } =
    toJumpMap tmcase_term

instance ToJumpMap (RST.TermCaseI pc) where
  toJumpMap RST.MkTermCaseI { tmcasei_term } =
    toJumpMap tmcasei_term

instance ToJumpMap RST.Command where
  toJumpMap (RST.Apply _ prd cns) =
    M.union (toJumpMap prd) (toJumpMap cns)
  toJumpMap (RST.Print _ prd cmd) =
    M.union (toJumpMap prd) (toJumpMap cmd)
  toJumpMap (RST.Read _ cns) = toJumpMap cns
  toJumpMap RST.Jump {} = M.empty
  toJumpMap (RST.Method _ _ _ subst) = toJumpMap subst
  toJumpMap RST.ExitSuccess {} = M.empty
  toJumpMap RST.ExitFailure {} = M.empty
  toJumpMap (RST.PrimOp _ _ subst) = toJumpMap subst
  toJumpMap (RST.CaseOfCmd _ _ tm cases) =
    M.unions (toJumpMap tm : (toJumpMap <$> cases))
  toJumpMap (RST.CaseOfI _ _ _ tm casesi) =
    M.unions (toJumpMap tm : (toJumpMap <$> casesi))
  toJumpMap (RST.CocaseOfCmd _ _ tm cases) =
    M.unions (toJumpMap tm : (toJumpMap <$> cases))
  toJumpMap (RST.CocaseOfI _ _ _ tm casesi) =
    M.unions (toJumpMap tm : (toJumpMap <$> casesi))


instance ToJumpMap (RST.Term pc) where
  toJumpMap RST.BoundVar {} = M.empty
  toJumpMap RST.FreeVar {} = M.empty
  toJumpMap (RST.Xtor _ _ _ _ subst) = toJumpMap subst
  toJumpMap (RST.XCase _ _ _ cases) = M.unions (toJumpMap <$> cases)
  toJumpMap (RST.MuAbs _ _ _ cmd) = toJumpMap cmd
  toJumpMap (RST.Semi _ _ _ _ subst tm) = M.union (toJumpMap tm) (toJumpMap subst)
  toJumpMap (RST.Dtor _ _ _ _ tm subst) = M.union (toJumpMap tm) (toJumpMap subst)
  toJumpMap (RST.CaseOf _ _ _ tm cases) = M.unions (toJumpMap tm : (toJumpMap <$> cases))
  toJumpMap (RST.CocaseOf _ _ _ tm cases) = M.unions (toJumpMap tm : (toJumpMap <$> cases))
  toJumpMap (RST.CaseI _ _ _ cases) = M.unions (toJumpMap <$> cases)
  toJumpMap (RST.CocaseI _ _ _ cases) = M.unions (toJumpMap <$> cases)
  toJumpMap (RST.Lambda _ _ _ tm) = toJumpMap tm
  toJumpMap RST.PrimLitI64 {} = M.empty
  toJumpMap RST.PrimLitF64 {} = M.empty
  toJumpMap RST.PrimLitChar {} = M.empty
  toJumpMap RST.PrimLitString {} = M.empty


---------------------------------------------------------------------------------
-- Converting Types to a JumpMap
---------------------------------------------------------------------------------

instance ToJumpMap (RST.VariantType pol) where
  toJumpMap (RST.CovariantType ty) = toJumpMap ty
  toJumpMap (RST.ContravariantType ty) = toJumpMap ty

instance ToJumpMap (RST.PrdCnsType pol) where
  toJumpMap (RST.PrdCnsType _ ty) = toJumpMap ty

instance ToJumpMap (RST.Typ pol) where
  toJumpMap RST.TyUniVar {} =
    M.empty
  toJumpMap RST.TySkolemVar {} = 
    M.empty
  toJumpMap RST.TyRecVar {} = 
    M.empty
  toJumpMap (RST.TyDataRefined loc _ tn xtors) =
    M.unions (M.fromList [(locToRange loc, toLocation tn)] : (toJumpMap <$> xtors))
  toJumpMap (RST.TyData _ _ xtors) =
    M.unions (toJumpMap <$> xtors)
  toJumpMap (RST.TyCodataRefined loc _ tn xtors) =
    M.unions (M.fromList [(locToRange loc, toLocation tn)] : (toJumpMap <$> xtors))
  toJumpMap (RST.TyCodata _ _ xtors) =
    M.unions (toJumpMap <$> xtors)
  toJumpMap (RST.TyNominal loc _ rn args) =
    M.unions (M.fromList [(locToRange loc, toLocation rn)] : (toJumpMap <$> args))
  toJumpMap (RST.TySyn loc _ rn _) =
    M.fromList [(locToRange loc, toLocation rn)]
  toJumpMap RST.TyBot {} = M.empty
  toJumpMap RST.TyTop {} = M.empty
  toJumpMap (RST.TyUnion _ ty1 ty2) =
    M.union (toJumpMap ty1) (toJumpMap ty2)
  toJumpMap (RST.TyInter _ ty1 ty2) =
    M.union (toJumpMap ty1) (toJumpMap ty2)
  toJumpMap (RST.TyRec _ _ _ ty) =
    toJumpMap ty
  toJumpMap RST.TyI64 {} = M.empty
  toJumpMap RST.TyF64 {} = M.empty
  toJumpMap RST.TyChar {} = M.empty
  toJumpMap RST.TyString {} = M.empty
  toJumpMap (RST.TyFlipPol _ ty) = toJumpMap ty

instance ToJumpMap (RST.XtorSig pol) where
  toJumpMap (RST.MkXtorSig _ ctx) =
    M.unions (toJumpMap <$> ctx)

instance ToJumpMap (RST.TypeScheme pol) where
  toJumpMap RST.TypeScheme { ts_monotype } =
    toJumpMap ts_monotype

---------------------------------------------------------------------------------
-- Converting programs to a JumpMap
---------------------------------------------------------------------------------

instance ToJumpMap RST.Module where
  toJumpMap RST.MkModule { mod_decls } = M.unions (toJumpMap <$> mod_decls)

instance ToJumpMap (RST.PrdCnsDeclaration pc) where
  toJumpMap RST.MkPrdCnsDeclaration { pcdecl_term, pcdecl_annot = Nothing } =
    toJumpMap pcdecl_term
  toJumpMap RST.MkPrdCnsDeclaration { pcdecl_term, pcdecl_annot = Just tys} =
    M.union (toJumpMap tys) (toJumpMap pcdecl_term)

instance ToJumpMap RST.CommandDeclaration where
  toJumpMap RST.MkCommandDeclaration { cmddecl_cmd } =
    toJumpMap cmddecl_cmd

instance ToJumpMap RST.TyOpDeclaration where
  toJumpMap RST.MkTyOpDeclaration { tyopdecl_loc, tyopdecl_res } =
    M.fromList [(locToRange tyopdecl_loc, toLocation tyopdecl_res)]

instance ToJumpMap RST.InstanceDeclaration where
  toJumpMap RST.MkInstanceDeclaration { instancedecl_cases } =
    M.unions $ toJumpMap <$> instancedecl_cases

instance ToJumpMap RST.Declaration where
  toJumpMap (RST.PrdCnsDecl _ decl) = toJumpMap decl
  toJumpMap (RST.CmdDecl decl) = toJumpMap decl
  toJumpMap RST.DataDecl {} = M.empty
  toJumpMap RST.XtorDecl {} = M.empty
  toJumpMap RST.ImportDecl {} = M.empty
  toJumpMap RST.SetDecl {} = M.empty
  toJumpMap (RST.TyOpDecl decl) = toJumpMap decl
  toJumpMap RST.ClassDecl {} = M.empty
  toJumpMap RST.InstanceDecl {} = M.empty
  toJumpMap RST.TySynDecl {} = M.empty


instance ToLocation RnTypeName where
  toLocation MkRnTypeName { rnTnLoc, rnTnFp } =
    let rng = locToRange rnTnLoc
    in  Location { _uri = Uri $ maybe "" T.pack rnTnFp
                 , _range = rng
                 }
