module LSP.Handler.JumpToDef ( jumpToDefHandler ) where

import Control.Monad.IO.Class ( MonadIO(liftIO) )
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T
import Data.List.NonEmpty qualified as NE
import Language.LSP.Types
    ( Uri(Uri),
      Range,
      SMethod(STextDocumentDefinition),
      RequestMessage(RequestMessage),
      ResponseError(..),
      TextDocumentIdentifier(TextDocumentIdentifier),
      type (|?)(InL),
      DefinitionParams(DefinitionParams),
      Location(..),
      Position,
      ErrorCode(InvalidRequest) )
import Language.LSP.Server
    (  requestHandler, Handlers, getConfig )
import System.Log.Logger ( debugM )

import LSP.Definition ( LSPMonad, LSPConfig (..), sendInfo )
import LSP.MegaparsecToLSP ( locToRange, lookupInRangeMap )
import Sugar.Desugar (Desugar(..))
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Names
import Syntax.RST.Types qualified as RST
import Syntax.RST.Program qualified as RST
import Translate.EmbedTST(EmbedTST(..))
import Data.IORef (readIORef)

jumpToDefHandler :: Handlers LSPMonad
jumpToDefHandler = requestHandler STextDocumentDefinition $ \req responder -> do
    let (RequestMessage _ _ _ (DefinitionParams (TextDocumentIdentifier uri) pos _ _)) = req
    liftIO $ debugM "lspserver.JumpToDefHandler" ("Received definition request: " <> show uri <> " at: " <> show pos)
    MkLSPConfig ref <- getConfig
    cache <- liftIO $ readIORef ref
    case M.lookup uri cache of
      Nothing -> do
        sendInfo ("Cache not initialized for: " <> T.pack (show uri))
        responder (Left (ResponseError { _code = InvalidRequest, _message = "", _xdata = Nothing}))
      Just mod -> responder (generateJumpToDef pos (embedCore (embedTST mod)))

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
  toJumpMap (RST.MkSubstitution subst) = M.unions (toJumpMap <$> subst)

instance ToJumpMap (RST.SubstitutionI pc) where
  toJumpMap (RST.MkSubstitutionI (subst1,_,subst2)) =
    M.unions ((toJumpMap <$> subst1) ++ (toJumpMap <$> subst2))

instance ToJumpMap RST.CmdCase where
  toJumpMap cmdcase =
    toJumpMap cmdcase.cmdcase_cmd

instance ToJumpMap RST.InstanceCase where
  toJumpMap icase =
    toJumpMap icase.instancecase_cmd

instance ToJumpMap (RST.TermCase pc) where
  toJumpMap tmcase =
    toJumpMap tmcase.tmcase_term

instance ToJumpMap (RST.TermCaseI pc) where
  toJumpMap icase =
    toJumpMap icase.tmcasei_term

instance ToJumpMap RST.Command where
  toJumpMap (RST.Apply _ prd cns) =
    M.union (toJumpMap prd) (toJumpMap cns)
  toJumpMap (RST.Print _ prd cmd) =
    M.union (toJumpMap prd) (toJumpMap cmd)
  toJumpMap (RST.Read _ cns) = toJumpMap cns
  toJumpMap RST.Jump {} = M.empty
  toJumpMap (RST.Method _ _ _ _ subst) = toJumpMap subst
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
  toJumpMap (RST.TyDataRefined loc _ _ tn xtors) =
    M.unions (M.fromList [(locToRange loc, toLocation tn)] : (toJumpMap <$> xtors))
  toJumpMap (RST.TyData _ _ xtors) =
    M.unions (toJumpMap <$> xtors)
  toJumpMap (RST.TyCodataRefined loc _ _ tn xtors) =
    M.unions (M.fromList [(locToRange loc, toLocation tn)] : (toJumpMap <$> xtors))
  toJumpMap (RST.TyCodata _ _ xtors) =
    M.unions (toJumpMap <$> xtors)
  toJumpMap (RST.TyNominal loc _ _ rn) = 
    M.fromList [(locToRange loc, toLocation rn)]
  toJumpMap (RST.TyApp _ _ ty args) = 
    M.unions (toJumpMap ty : (NE.toList $ toJumpMap <$> args))
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
  toJumpMap (RST.TyKindAnnot _ ty) = toJumpMap ty

instance ToJumpMap (RST.XtorSig pol) where
  toJumpMap (RST.MkXtorSig _ ctx) =
    M.unions (toJumpMap <$> ctx)

instance ToJumpMap (RST.TypeScheme pol) where
  toJumpMap ts =
    toJumpMap ts.ts_monotype

---------------------------------------------------------------------------------
-- Converting programs to a JumpMap
---------------------------------------------------------------------------------

instance ToJumpMap RST.Module where
  toJumpMap mod = M.unions (toJumpMap <$> mod.mod_decls)

instance ToJumpMap (RST.PrdCnsDeclaration pc) where
  toJumpMap decl =
    case decl.pcdecl_annot of
      Nothing -> toJumpMap decl.pcdecl_term
      Just tys -> M.union (toJumpMap tys) (toJumpMap decl.pcdecl_term)

instance ToJumpMap RST.CommandDeclaration where
  toJumpMap decl=
    toJumpMap decl.cmddecl_cmd

instance ToJumpMap RST.TyOpDeclaration where
  toJumpMap decl =
    M.fromList [(locToRange decl.tyopdecl_loc, toLocation decl.tyopdecl_res)]

instance ToJumpMap RST.InstanceDeclaration where
  toJumpMap decl =
    M.unions $ toJumpMap <$> decl.instancedecl_cases

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
  toLocation rn =
    let rng = locToRange rn.rnTnLoc
    in  Location { _uri = Uri $ maybe "" T.pack rn.rnTnFp
                 , _range = rng
                 }
