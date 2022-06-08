module Resolution.Program (resolveProgram, resolveDecl) where

import Control.Monad.Reader
import Control.Monad.Except (throwError)
import Data.Map (Map)
import Data.Map qualified as M

import Errors
import Resolution.Definition
import Resolution.SymbolTable
import Resolution.Terms (resolveTerm, resolveCommand)
import Resolution.Types (resolveTypeScheme, resolveXTorSigs, resolveTyp)
import Syntax.CST.Program qualified as CST
import Syntax.Common.TypesUnpol qualified as CST
import Syntax.RST.Program qualified as RST
import Syntax.Common.TypesPol qualified as RST
import Syntax.Common
import Utils (Loc)
import Syntax.Common.TypesUnpol (XtorSig (sig_args), PrdCnsTyp (PrdType, CnsType), Typ (..))
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.Text as T

resolveXtors :: [CST.XtorSig]
           -> ResolverM ([RST.XtorSig Pos], [RST.XtorSig Neg])
resolveXtors sigs = do
    posSigs <- resolveXTorSigs PosRep sigs
    negSigs <- resolveXTorSigs NegRep sigs
    pure (posSigs, negSigs)

checkVarianceTyp :: Loc -> Variance -> PolyKind -> CST.Typ -> ResolverM ()
checkVarianceTyp loc var polyKind (TyVar _loc' tVar) =
  case lookupPolyKindVariance tVar polyKind of
    --  Nothing   -> throwError (OtherError (Just loc) $ "Type variable not bound by declaration: " <> T.pack (show tVar))
    Nothing   -> return ()
    Just var' -> if var == var'
                 then return ()
                 else throwError (OtherError (Just loc) $ "Variance mismatch for variable " <> T.pack (show tVar) <> ":\nFound: " <> T.pack (show var) <> "\nRequired: " <> T.pack (show var'))
checkVarianceTyp loc var polyKind (TyXData _loc' dataCodata _mTypeName xtorSigs) = do
  let var' = var <> case dataCodata of
                      Data   -> Covariant
                      Codata -> Contravariant
  sequence_ $ checkVarianceXtor loc var' polyKind <$> xtorSigs
checkVarianceTyp loc var polyKind (TyNominal _loc' tyName tys) = do
  NominalResult _ _ _ polyKind' <- lookupTypeConstructor loc tyName
  go ((\(v,_,_) -> v) <$> kindArgs polyKind') tys
  where
    go :: [Variance] -> [Typ] -> ResolverM ()
    go [] []          = return ()
    go (v:vs) (t:ts)  = do
      checkVarianceTyp loc (v <> var) polyKind t
      go vs ts
    go [] (_:_)       = throwError (OtherError (Just loc) $ "Type Constructor " <> T.pack (show tyName) <> " is applied to too many arguments")
    go (_:_) []       = throwError (OtherError (Just loc) $ "Type Constructor " <> T.pack (show tyName) <> " is applied to too few arguments")
checkVarianceTyp loc var polyKind (TyRec _loc' _tVar ty) =
  checkVarianceTyp loc var polyKind ty
checkVarianceTyp _loc _var _polyKind (TyTop _loc') = return ()
checkVarianceTyp _loc _var _polyKind (TyBot _loc') = return ()
checkVarianceTyp _loc _var _polyKind (TyPrim _loc' _primitiveType) = return ()
checkVarianceTyp loc var polyKind (TyBinOpChain ty tys) = do
  -- see comments for TyBinOp
  checkVarianceTyp loc var polyKind ty
  case tys of
    ((_,_,ty') :| tys') -> do
      checkVarianceTyp loc var polyKind ty'
      sequence_ $ (\(_,_,ty) -> checkVarianceTyp loc var polyKind ty) <$> tys'
checkVarianceTyp loc var polyKind (TyBinOp _loc' ty _binOp ty') = do
  -- this might need to check whether only allowed binOps are used here (i.e. forbid data Union +a +b { Union(a \/ b) } )
  -- also, might need variance check
  checkVarianceTyp loc var polyKind ty
  checkVarianceTyp loc var polyKind ty'
checkVarianceTyp loc var polyKind (TyParens _loc' ty) = checkVarianceTyp loc var polyKind ty

checkVarianceXtor :: Loc -> Variance -> PolyKind -> XtorSig -> ResolverM ()
checkVarianceXtor loc var polyKind xtor = do
  sequence_ $ f <$> sig_args xtor
  where
    f :: PrdCnsTyp -> ResolverM ()
    f (PrdType ty) = checkVarianceTyp loc (Covariant     <> var) polyKind ty
    f (CnsType ty) = checkVarianceTyp loc (Contravariant <> var) polyKind ty

checkVarianceDataDecl :: Loc -> PolyKind -> DataCodata -> [XtorSig] -> ResolverM ()
checkVarianceDataDecl loc polyKind pol xtors = do
  case pol of
    Data   -> sequence_ $ checkVarianceXtor loc Covariant     polyKind <$> xtors
    Codata -> sequence_ $ checkVarianceXtor loc Contravariant polyKind <$> xtors

resolveDataDecl :: Loc -> CST.DataDecl -> ResolverM RST.DataDecl
resolveDataDecl loc CST.NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors } = do
  NominalResult data_name' _ _ _ <- lookupTypeConstructor loc data_name
  -- Default the kind if none was specified:
  let polyKind = case data_kind of
                    Nothing -> MkPolyKind [] (case data_polarity of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
  checkVarianceDataDecl loc polyKind data_polarity data_xtors
  -- Lower the xtors in the adjusted environment (necessary for lowering xtors of refinement types)
  let g :: TypeNameResolve -> TypeNameResolve
      g (SynonymResult tn ty) = SynonymResult tn ty
      g (NominalResult tn dc _ polykind) = NominalResult tn dc NotRefined polykind
  let f :: Map ModuleName SymbolTable -> Map ModuleName SymbolTable
      f x = M.fromList (fmap (\(mn, st) -> (mn, st { typeNameMap = M.adjust g data_name (typeNameMap st) })) (M.toList x))
  xtors <- local f (resolveXtors data_xtors)
  -- Create the new data declaration
  let dcl = RST.NominalDecl
                { data_refined = data_refined
                , data_name = data_name'
                , data_polarity = data_polarity
                , data_kind = polyKind
                , data_xtors = xtors
                }
  pure dcl

resolveAnnot :: PrdCnsRep pc -> CST.TypeScheme -> ResolverM (RST.TypeScheme (PrdCnsToPol pc))
resolveAnnot PrdRep ts = resolveTypeScheme PosRep ts
resolveAnnot CnsRep ts = resolveTypeScheme NegRep ts

resolveMaybeAnnot :: PrdCnsRep pc -> Maybe (CST.TypeScheme) -> ResolverM (Maybe (RST.TypeScheme (PrdCnsToPol pc)))
resolveMaybeAnnot _ Nothing = pure Nothing
resolveMaybeAnnot pc (Just annot) = Just <$> resolveAnnot pc annot

resolveDecl :: CST.Declaration -> ResolverM RST.Declaration
resolveDecl (CST.PrdCnsDecl loc doc Prd isrec fv annot tm) =
  RST.PrdCnsDecl loc doc PrdRep isrec fv <$> (resolveMaybeAnnot PrdRep annot) <*> (resolveTerm PrdRep tm)
resolveDecl (CST.PrdCnsDecl loc doc Cns isrec fv annot tm) =
  RST.PrdCnsDecl loc doc CnsRep isrec fv <$> (resolveMaybeAnnot CnsRep annot) <*> (resolveTerm CnsRep tm)
resolveDecl (CST.CmdDecl loc doc fv cmd) =
  RST.CmdDecl loc doc fv <$> (resolveCommand cmd)
resolveDecl (CST.DataDecl loc doc dd) = do
  lowered <- resolveDataDecl loc dd
  pure $ RST.DataDecl loc doc lowered
resolveDecl (CST.XtorDecl loc doc dc xt args ret) = do
  let ret' = case ret of
               Just eo -> eo
               Nothing -> case dc of Data -> CBV; Codata -> CBN
  pure $ RST.XtorDecl loc doc dc xt args ret'
resolveDecl (CST.ImportDecl loc doc mod) = do
  pure $ RST.ImportDecl loc doc mod
resolveDecl (CST.SetDecl loc doc txt) =
  pure $ RST.SetDecl loc doc txt
resolveDecl (CST.TyOpDecl loc doc op prec assoc tyname) = do
  NominalResult tyname' _ _ _ <- lookupTypeConstructor loc tyname
  pure $ RST.TyOpDecl loc doc op prec assoc tyname'
resolveDecl (CST.TySynDecl loc doc nm ty) = do
  typ <- resolveTyp PosRep ty
  tyn <- resolveTyp NegRep ty
  pure (RST.TySynDecl loc doc nm (typ, tyn))
resolveDecl CST.ParseErrorDecl =
  throwError (OtherError Nothing "Unreachable: ParseErrorDecl cannot be parsed")

resolveProgram :: CST.Program -> ResolverM RST.Program
resolveProgram = sequence . fmap resolveDecl
