module Resolution.Program (resolveProgram, resolveDecl) where

import Control.Monad.Reader
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T

import Errors
import Resolution.Definition
import Resolution.SymbolTable
import Resolution.Terms (resolveTerm, resolveCommand, resolveInstanceCases)
import Resolution.Types (resolveTypeScheme, resolveXTorSigs, resolveTyp)
import Syntax.CST.Program qualified as CST
import Syntax.Common.TypesUnpol qualified as CST
import Syntax.Common.TypesUnpol (XtorSig (sig_args), PrdCnsTyp (PrdType, CnsType), Typ (..))
import Syntax.RST.Program qualified as RST
import Syntax.Common.TypesPol qualified as RST
import Syntax.Common
import Utils (Loc, defaultLoc)


---------------------------------------------------------------------------------
-- Data Declarations
---------------------------------------------------------------------------------

resolveXtors :: [CST.XtorSig]
           -> ResolverM ([RST.XtorSig Pos], [RST.XtorSig Neg])
resolveXtors sigs = do
    posSigs <- resolveXTorSigs PosRep sigs
    negSigs <- resolveXTorSigs NegRep sigs
    pure (posSigs, negSigs)

checkVarianceTyp :: Loc -> Variance -> PolyKind -> CST.Typ -> ResolverM ()
checkVarianceTyp _ _ tv(TyUniVar loc _) =
  throwOtherError loc ["The Unification Variable " <> T.pack (show  tv) <> " should not appear in the program at this point"]
checkVarianceTyp loc var polyKind (TySkolemVar _loc' tVar) =
  case lookupPolyKindVariance tVar polyKind of
    -- The following line does not work correctly if the data declaration contains recursive types in the arguments of an xtor.
    Nothing   -> throwOtherError loc ["Type variable not bound by declaration: " <> T.pack (show tVar)]
    Just var' -> if var == var'
                 then return ()
                 else throwOtherError loc ["Variance mismatch for variable " <> T.pack (show tVar) <> ":\nFound: " <> T.pack (show var) <> "\nRequired: " <> T.pack (show var')]
checkVarianceTyp loc var polyKind (TyXData _loc' dataCodata  xtorSigs) = do
  let var' = var <> case dataCodata of
                      Data   -> Covariant
                      Codata -> Contravariant
  sequence_ $ checkVarianceXtor loc var' polyKind <$> xtorSigs
checkVarianceTyp loc var polyKind (TyXRefined _loc' dataCodata  _tn xtorSigs) = do
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
    go [] (_:_)       = throwOtherError loc ["Type Constructor " <> T.pack (show tyName) <> " is applied to too many arguments"]
    go (_:_) []       = throwOtherError loc ["Type Constructor " <> T.pack (show tyName) <> " is applied to too few arguments"]
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

resolveDataDecl :: CST.DataDecl -> ResolverM RST.DataDecl
resolveDataDecl CST.NominalDecl { data_loc, data_doc, data_refined, data_name, data_polarity, data_kind, data_xtors } = do
  NominalResult data_name' _ _ _ <- lookupTypeConstructor data_loc data_name
  -- Default the kind if none was specified:
  let polyKind = case data_kind of
                    Nothing -> MkPolyKind [] (case data_polarity of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
  checkVarianceDataDecl data_loc polyKind data_polarity data_xtors
  -- Lower the xtors in the adjusted environment (necessary for lowering xtors of refinement types)
  let g :: TypeNameResolve -> TypeNameResolve
      g (SynonymResult tn ty) = SynonymResult tn ty
      g (NominalResult tn dc _ polykind) = NominalResult tn dc NotRefined polykind
  let f :: Map ModuleName SymbolTable -> Map ModuleName SymbolTable
      f x = M.fromList (fmap (\(mn, st) -> (mn, st { typeNameMap = M.adjust g data_name (typeNameMap st) })) (M.toList x))
  xtors <- local f (resolveXtors data_xtors)
  -- Create the new data declaration
  let dcl = RST.NominalDecl
                { data_loc = data_loc
                , data_doc = data_doc
                , data_refined = data_refined
                , data_name = data_name'
                , data_polarity = data_polarity
                , data_kind = polyKind
                , data_xtors = xtors
                }
  pure dcl

---------------------------------------------------------------------------------
-- Producer / Consumer Declarations
---------------------------------------------------------------------------------

resolveAnnot :: PrdCnsRep pc
             -> CST.TypeScheme
             -> ResolverM (RST.TypeScheme (PrdCnsToPol pc))
resolveAnnot PrdRep ts = resolveTypeScheme PosRep ts
resolveAnnot CnsRep ts = resolveTypeScheme NegRep ts

resolveMaybeAnnot :: PrdCnsRep pc
                  -> Maybe CST.TypeScheme
                  -> ResolverM (Maybe (RST.TypeScheme (PrdCnsToPol pc)))
resolveMaybeAnnot _ Nothing = pure Nothing
resolveMaybeAnnot pc (Just annot) = Just <$> resolveAnnot pc annot

resolvePrdCnsDeclaration :: PrdCnsRep pc
                         -> CST.PrdCnsDeclaration
                         -> ResolverM (RST.PrdCnsDeclaration pc)
resolvePrdCnsDeclaration pcrep CST.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term } = do
  pcdecl_annot' <- resolveMaybeAnnot pcrep pcdecl_annot
  pcdecl_term' <- resolveTerm pcrep pcdecl_term
  pure $ RST.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                                 , pcdecl_doc = pcdecl_doc
                                 , pcdecl_pc = pcrep
                                 , pcdecl_isRec =pcdecl_isRec
                                 , pcdecl_name = pcdecl_name
                                 , pcdecl_annot = pcdecl_annot'
                                 , pcdecl_term = pcdecl_term'
                                 }

---------------------------------------------------------------------------------
-- Command Declarations
---------------------------------------------------------------------------------

resolveCommandDeclaration :: CST.CommandDeclaration
                          -> ResolverM RST.CommandDeclaration
resolveCommandDeclaration CST.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } = do
  cmddecl_cmd' <- resolveCommand cmddecl_cmd
  pure $ RST.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                                  , cmddecl_doc = cmddecl_doc
                                  , cmddecl_name = cmddecl_name
                                  , cmddecl_cmd= cmddecl_cmd'
                                  }

---------------------------------------------------------------------------------
-- Structural Xtor Declaration
---------------------------------------------------------------------------------

resolveStructuralXtorDeclaration :: CST.StructuralXtorDeclaration
                                 -> ResolverM RST.StructuralXtorDeclaration
resolveStructuralXtorDeclaration CST.MkStructuralXtorDeclaration {strxtordecl_loc, strxtordecl_doc, strxtordecl_xdata, strxtordecl_name, strxtordecl_arity, strxtordecl_evalOrder} = do
  let evalOrder = case strxtordecl_evalOrder of
                  Just eo -> eo
                  Nothing -> case strxtordecl_xdata of Data -> CBV; Codata -> CBN
  pure $ RST.MkStructuralXtorDeclaration { strxtordecl_loc = strxtordecl_loc
                                         , strxtordecl_doc = strxtordecl_doc
                                         , strxtordecl_xdata = strxtordecl_xdata
                                         , strxtordecl_name = strxtordecl_name
                                         , strxtordecl_arity = strxtordecl_arity
                                         , strxtordecl_evalOrder = evalOrder
                                         }

---------------------------------------------------------------------------------
-- Type Operator Declaration
---------------------------------------------------------------------------------

resolveTyOpDeclaration :: CST.TyOpDeclaration
                       -> ResolverM RST.TyOpDeclaration
resolveTyOpDeclaration CST.MkTyOpDeclaration { tyopdecl_loc, tyopdecl_doc, tyopdecl_sym, tyopdecl_prec, tyopdecl_assoc, tyopdecl_res } = do
  NominalResult tyname' _ _ _ <- lookupTypeConstructor tyopdecl_loc tyopdecl_res
  pure RST.MkTyOpDeclaration { tyopdecl_loc = tyopdecl_loc
                             , tyopdecl_doc = tyopdecl_doc
                             , tyopdecl_sym = tyopdecl_sym
                             , tyopdecl_prec = tyopdecl_prec
                             , tyopdecl_assoc = tyopdecl_assoc
                             , tyopdecl_res = tyname'
                             }

---------------------------------------------------------------------------------
-- Type Synonym Declaration
---------------------------------------------------------------------------------

resolveTySynDeclaration :: CST.TySynDeclaration
                        -> ResolverM RST.TySynDeclaration
resolveTySynDeclaration CST.MkTySynDeclaration { tysyndecl_loc, tysyndecl_doc, tysyndecl_name, tysyndecl_res } = do
  typ <- resolveTyp PosRep tysyndecl_res
  tyn <- resolveTyp NegRep tysyndecl_res
  pure RST.MkTySynDeclaration { tysyndecl_loc = tysyndecl_loc
                              , tysyndecl_doc = tysyndecl_doc
                              , tysyndecl_name = tysyndecl_name
                              , tysyndecl_res = (typ, tyn)
                              }

---------------------------------------------------------------------------------
-- Type Class Declaration
---------------------------------------------------------------------------------

resolveClassDeclaration :: CST.ClassDeclaration 
                        -> ResolverM RST.ClassDeclaration
resolveClassDeclaration CST.MkClassDeclaration { classdecl_loc, classdecl_doc, classdecl_name, classdecl_kinds, classdecl_xtors } = do
  let go :: (PrdCns, Typ) -> ResolverM (PrdCns, RST.Typ 'Pos, RST.Typ 'Neg)
      go (prdcns, typ) = do
            typos <- resolveTyp PosRep typ
            tyneg <- resolveTyp NegRep typ
            pure (prdcns, typos, tyneg)
      go' :: (XtorName, [(PrdCns, Typ)]) -> ResolverM (XtorName, [(PrdCns, RST.Typ 'Pos, RST.Typ 'Neg)])
      go' (xtor, typs) = do
            types <- forM typs go
            pure (xtor, types)
  xtorRes <- forM classdecl_xtors go'
  pure RST.MkClassDeclaration { classdecl_loc = classdecl_loc
                              , classdecl_doc = classdecl_doc
                              , classdecl_name = classdecl_name
                              , classdecl_kinds = classdecl_kinds
                              , classdecl_xtors = xtorRes
                              }

---------------------------------------------------------------------------------
-- Instance Declaration
---------------------------------------------------------------------------------

resolveInstanceDeclaration :: CST.InstanceDeclaration 
                        -> ResolverM RST.InstanceDeclaration
resolveInstanceDeclaration CST.MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_typ, instancedecl_cases } = do
  typ <- resolveTyp PosRep instancedecl_typ
  tyn <- resolveTyp NegRep instancedecl_typ
  tc <- resolveInstanceCases instancedecl_cases
  pure RST.MkInstanceDeclaration { instancedecl_loc = instancedecl_loc
                                 , instancedecl_doc = instancedecl_doc
                                 , instancedecl_name = instancedecl_name
                                 , instancedecl_typ = (typ, tyn)
                                 , instancedecl_cases = tc
                                 }

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

resolveDecl :: CST.Declaration -> ResolverM RST.Declaration
resolveDecl (CST.PrdCnsDecl decl) = do
  case CST.pcdecl_pc decl of
    Prd -> do
      decl' <- resolvePrdCnsDeclaration PrdRep decl
      pure (RST.PrdCnsDecl PrdRep decl')
    Cns -> do
      decl' <- resolvePrdCnsDeclaration CnsRep decl
      pure (RST.PrdCnsDecl CnsRep decl')
resolveDecl (CST.CmdDecl decl) = do
  decl' <- resolveCommandDeclaration decl
  pure (RST.CmdDecl decl')
resolveDecl (CST.DataDecl decl) = do
  lowered <- resolveDataDecl decl
  pure $ RST.DataDecl lowered
resolveDecl (CST.XtorDecl decl) = do
  decl' <- resolveStructuralXtorDeclaration decl
  pure $ RST.XtorDecl decl'
resolveDecl (CST.ImportDecl decl) = do
  pure $ RST.ImportDecl decl
resolveDecl (CST.SetDecl decl) =
  pure $ RST.SetDecl decl
resolveDecl (CST.TyOpDecl decl) = do
  decl' <- resolveTyOpDeclaration decl
  pure $ RST.TyOpDecl decl'
resolveDecl (CST.TySynDecl decl) = do
  decl' <- resolveTySynDeclaration decl
  pure (RST.TySynDecl decl')
resolveDecl (CST.ClassDecl decl) = do
  decl' <- resolveClassDeclaration decl
  pure (RST.ClassDecl decl')
resolveDecl (CST.InstanceDecl decl) = do
  decl' <- resolveInstanceDeclaration decl
  pure (RST.InstanceDecl decl')
resolveDecl CST.ParseErrorDecl =
  throwOtherError defaultLoc ["Unreachable: ParseErrorDecl cannot be parsed"]

resolveProgram :: CST.Program -> ResolverM RST.Program
resolveProgram = mapM resolveDecl
