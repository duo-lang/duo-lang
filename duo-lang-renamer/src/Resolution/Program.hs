module Resolution.Program (resolveModule, resolveDecl) where

import Control.Monad.Reader
import Control.Monad.Except
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.List.NonEmpty qualified as NE
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T


import Errors.Renamer
import Resolution.Definition
import Resolution.SymbolTable
import Resolution.Terms (resolveTerm, resolveCommand, resolveInstanceCase)
import Resolution.Types (resolveTypeScheme, resolveXTorSigs, resolveTyp, resolveMethodSigs)
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.RST.Program qualified as RST
import Syntax.RST.Program (PrdCnsToPol)
import Syntax.RST.Types qualified as RST
import Syntax.RST.Types (Polarity(..), PolarityRep(..))
import Syntax.CST.Kinds
import Syntax.CST.Names
import Loc (Loc, defaultLoc)



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
checkVarianceTyp _ _ tv(CST.TyUniVar loc _) =
  throwError (UnknownResolutionError loc ("The Unification Variable " <> T.pack (show tv) <> " should not appear in the program at this point"))
checkVarianceTyp _ var polyKind (CST.TySkolemVar loc tVar) =
  case lookupPolyKindVariance tVar polyKind of
    -- The following line does not work correctly if the data declaration contains recursive types in the arguments of an xtor.
    Nothing   -> throwError (UnknownResolutionError loc ("Type variable not bound by declaration: " <> T.pack (show tVar)))
    Just var' -> if var == var'
                 then return ()
                 else throwError (UnknownResolutionError loc ("Variance mismatch for variable " <> T.pack (show tVar) <> ":\n"
                                          <> "Found: " <> T.pack (show var) <> "\n"
                                          <> "Required: " <> T.pack (show var')
                 ))
checkVarianceTyp loc var polyKind (CST.TyXData _loc' dataCodata  xtorSigs) = do
  let var' = var <> case dataCodata of
                      CST.Data   -> Covariant
                      CST.Codata -> Contravariant
  sequence_ $ checkVarianceXtor loc var' polyKind <$> xtorSigs
checkVarianceTyp loc var polyKind (CST.TyXRefined _loc' dataCodata  _tn _ xtorSigs) = do
  let var' = var <> case dataCodata of
                      CST.Data   -> Covariant
                      CST.Codata -> Contravariant
  sequence_ $ checkVarianceXtor loc var' polyKind <$> xtorSigs
checkVarianceTyp loc var polyKind (CST.TyApp _ (CST.TyNominal _loc' tyName) tys) = do

  NominalResult _ _ _ polyKind' <- lookupTypeConstructor loc tyName
  go ((\(v,_,_) -> v) <$> polyKind'.kindArgs) (NE.toList tys)
  where
    go :: [Variance] -> [CST.Typ] -> ResolverM ()
    go [] []          = return ()
    go (v:vs) (t:ts)  = do
      checkVarianceTyp loc (v <> var) polyKind t
      go vs ts
    go [] (_:_)       = throwError (UnknownResolutionError loc ("Type Constructor " <> T.pack (show tyName) <> " is applied to too many arguments"))
    go (_:_) []       = throwError (UnknownResolutionError loc ("Type Constructor " <> T.pack (show tyName) <> " is applied to too few arguments"))
checkVarianceTyp loc _ _ (CST.TyNominal _loc' tyName) = do
  NominalResult _ _ _ polyKnd' <- lookupTypeConstructor loc tyName
  case polyKnd'.kindArgs of 
    [] -> return () 
    _ -> throwError (UnknownResolutionError loc ("Type Constructor " <> T.pack (show tyName) <> " is applied to too few arguments"))
checkVarianceTyp loc var polyknd (CST.TyApp loc' (CST.TyParens _ ty) args) = checkVarianceTyp loc var polyknd (CST.TyApp loc' ty args)
checkVarianceTyp loc var polyknd (CST.TyApp loc' (CST.TyKindAnnot _ ty) args) = checkVarianceTyp loc var polyknd (CST.TyApp loc' ty args)
checkVarianceTyp loc _ _ CST.TyApp{} = 
  throwError (UnknownResolutionError loc "Types can only be applied to nominal types")
checkVarianceTyp loc var polyKind (CST.TyRec _loc' _tVar ty) =
  checkVarianceTyp loc var polyKind ty
checkVarianceTyp _loc _var _polyKind (CST.TyTop _loc') = return ()
checkVarianceTyp _loc _var _polyKind (CST.TyBot _loc') = return ()
checkVarianceTyp _loc _var _polyKind (CST.TyI64 _loc') = return ()
checkVarianceTyp _loc _var _polyKind (CST.TyF64 _loc') = return ()
checkVarianceTyp _loc _var _polyKind (CST.TyChar _loc') = return ()
checkVarianceTyp _loc _var _polyKind (CST.TyString _loc') = return ()
checkVarianceTyp loc var polyKind (CST.TyBinOpChain ty tys) = do
  -- see comments for TyBinOp
  checkVarianceTyp loc var polyKind ty
  case tys of
    ((_,_,ty') :| tys') -> do
      checkVarianceTyp loc var polyKind ty'
      sequence_ $ (\(_,_,ty) -> checkVarianceTyp loc var polyKind ty) <$> tys'
checkVarianceTyp loc var polyKind (CST.TyBinOp _loc' ty _binOp ty') = do
  -- this might need to check whether only allowed binOps are used here (i.e. forbid data Union +a +b { Union(a \/ b) } )
  -- also, might need variance check
  checkVarianceTyp loc var polyKind ty
  checkVarianceTyp loc var polyKind ty'
checkVarianceTyp loc var polyKind (CST.TyParens _loc' ty) = checkVarianceTyp loc var polyKind ty
checkVarianceTyp loc var polyKind (CST.TyKindAnnot _ ty) = checkVarianceTyp loc var polyKind ty

checkVarianceXtor :: Loc -> Variance -> PolyKind -> CST.XtorSig -> ResolverM ()
checkVarianceXtor loc var polyKind xtor = do
  sequence_ $ f <$> xtor.sig_args
  where
    f :: CST.PrdCnsTyp -> ResolverM ()
    f (CST.PrdType ty) = checkVarianceTyp loc (Covariant     <> var) polyKind ty
    f (CST.CnsType ty) = checkVarianceTyp loc (Contravariant <> var) polyKind ty

checkVarianceDataDecl :: Loc -> PolyKind -> CST.DataCodata -> [CST.XtorSig] -> ResolverM ()
checkVarianceDataDecl loc polyKind pol xtors = do
  case pol of
    CST.Data   -> sequence_ $ checkVarianceXtor loc Covariant     polyKind <$> xtors
    CST.Codata -> sequence_ $ checkVarianceXtor loc Contravariant polyKind <$> xtors

resolveDataDecl :: CST.DataDecl -> ResolverM RST.DataDecl
resolveDataDecl decl = do
  case decl.data_refined of
    CST.NotRefined -> do
      -------------------------------------------------------------------------
      -- Nominal Data Type
      -------------------------------------------------------------------------
      NominalResult data_name' _ _ _ <- lookupTypeConstructor decl.data_loc decl.data_name
      -- Default the kind if none was specified:
      let polyKind = case decl.data_kind of
                        Nothing -> MkPolyKind [] (case decl.data_polarity of CST.Data -> CBV; CST.Codata -> CBN)
                        Just knd -> knd
      checkVarianceDataDecl decl.data_loc polyKind decl.data_polarity decl.data_xtors
      xtors <- resolveXtors decl.data_xtors
      pure RST.NominalDecl { data_loc = decl.data_loc
                           , data_doc = decl.data_doc
                           , data_name = data_name'
                           , data_polarity = decl.data_polarity
                           , data_kind = polyKind
                           , data_xtors = xtors
                           }
    CST.Refined -> do
      -------------------------------------------------------------------------
      -- Refinement Data Type
      -------------------------------------------------------------------------
      NominalResult data_name' _ _ _ <- lookupTypeConstructor decl.data_loc decl.data_name
      -- Default the kind if none was specified:
      polyKind <- case decl.data_kind of
                        Nothing -> pure $ MkPolyKind [] (case decl.data_polarity of CST.Data -> CBV; CST.Codata -> CBN)
                        Just knd -> pure knd
      checkVarianceDataDecl decl.data_loc polyKind decl.data_polarity decl.data_xtors
      -- Lower the xtors in the adjusted environment (necessary for lowering xtors of refinement types)
      let g :: TypeNameResolve -> TypeNameResolve
          g (SynonymResult tn ty) = SynonymResult tn ty
          g (NominalResult tn dc _ polykind) = NominalResult tn dc CST.NotRefined polykind

          f :: Map ModuleName SymbolTable -> Map ModuleName SymbolTable
          f x = M.fromList (fmap (\(mn, st) -> (mn, st { typeNameMap = M.adjust g decl.data_name st.typeNameMap })) (M.toList x))

          h :: ResolveReader -> ResolveReader
          h r = r { rr_modules = f r.rr_modules }
      (xtorsPos, xtorsNeg) <- local h (resolveXtors decl.data_xtors)
      pure RST.RefinementDecl { data_loc = decl.data_loc
                              , data_doc = decl.data_doc
                              , data_name = data_name'
                              , data_polarity = decl.data_polarity
                              , data_kind = polyKind
                              , data_xtors = (xtorsPos, xtorsNeg)
                              }

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
resolvePrdCnsDeclaration pcrep decl = do
  pcdecl_annot' <- resolveMaybeAnnot pcrep decl.pcdecl_annot
  pcdecl_term' <- resolveTerm pcrep decl.pcdecl_term
  pure $ RST.MkPrdCnsDeclaration { pcdecl_loc = decl.pcdecl_loc
                                 , pcdecl_doc = decl.pcdecl_doc
                                 , pcdecl_pc = pcrep
                                 , pcdecl_isRec = decl.pcdecl_isRec
                                 , pcdecl_name = decl.pcdecl_name
                                 , pcdecl_annot = pcdecl_annot'
                                 , pcdecl_term = pcdecl_term'
                                 }

---------------------------------------------------------------------------------
-- Command Declarations
---------------------------------------------------------------------------------

resolveCommandDeclaration :: CST.CommandDeclaration
                          -> ResolverM RST.CommandDeclaration
resolveCommandDeclaration decl = do
  cmddecl_cmd' <- resolveCommand decl.cmddecl_cmd
  pure $ RST.MkCommandDeclaration { cmddecl_loc = decl.cmddecl_loc
                                  , cmddecl_doc = decl.cmddecl_doc
                                  , cmddecl_name = decl.cmddecl_name
                                  , cmddecl_cmd= cmddecl_cmd'
                                  }

---------------------------------------------------------------------------------
-- Structural Xtor Declaration
---------------------------------------------------------------------------------

resolveStructuralXtorDeclaration :: CST.StructuralXtorDeclaration
                                 -> ResolverM RST.StructuralXtorDeclaration
resolveStructuralXtorDeclaration decl = do
  let evalOrder = case decl.strxtordecl_evalOrder of
                  Just eo -> eo
                  Nothing -> case decl.strxtordecl_xdata of CST.Data -> CBV; CST.Codata -> CBN
  pure $ RST.MkStructuralXtorDeclaration { strxtordecl_loc = decl.strxtordecl_loc
                                         , strxtordecl_doc = decl.strxtordecl_doc
                                         , strxtordecl_xdata = decl.strxtordecl_xdata
                                         , strxtordecl_name = decl.strxtordecl_name
                                         , strxtordecl_arity = decl.strxtordecl_arity
                                         , strxtordecl_evalOrder = evalOrder
                                         }

---------------------------------------------------------------------------------
-- Type Operator Declaration
---------------------------------------------------------------------------------

resolveTyOpDeclaration :: CST.TyOpDeclaration
                       -> ResolverM RST.TyOpDeclaration
resolveTyOpDeclaration decl= do
  NominalResult tyname' _ _ _ <- lookupTypeConstructor decl.tyopdecl_loc decl.tyopdecl_res
  pure RST.MkTyOpDeclaration { tyopdecl_loc = decl.tyopdecl_loc
                             , tyopdecl_doc = decl.tyopdecl_doc
                             , tyopdecl_sym = decl.tyopdecl_sym
                             , tyopdecl_prec = decl.tyopdecl_prec
                             , tyopdecl_assoc = decl.tyopdecl_assoc
                             , tyopdecl_res = tyname'
                             }

---------------------------------------------------------------------------------
-- Type Synonym Declaration
---------------------------------------------------------------------------------

resolveTySynDeclaration :: CST.TySynDeclaration
                        -> ResolverM RST.TySynDeclaration
resolveTySynDeclaration decl = do
  typ <- resolveTyp PosRep decl.tysyndecl_res
  tyn <- resolveTyp NegRep decl.tysyndecl_res
  pure RST.MkTySynDeclaration { tysyndecl_loc = decl.tysyndecl_loc
                              , tysyndecl_doc = decl.tysyndecl_doc
                              , tysyndecl_name = decl.tysyndecl_name
                              , tysyndecl_res = (typ, tyn)
                              }

---------------------------------------------------------------------------------
-- Type Class Declaration
---------------------------------------------------------------------------------

checkVarianceClassDeclaration :: Loc -> PolyKind -> [CST.XtorSig] -> ResolverM ()
checkVarianceClassDeclaration loc kinds = mapM_ (checkVarianceXtor loc Covariant kinds)

resolveMethods :: [CST.XtorSig]
           -> ResolverM ([RST.MethodSig Pos], [RST.MethodSig Neg])
resolveMethods sigs = do
    posSigs <- resolveMethodSigs PosRep sigs
    negSigs <- resolveMethodSigs NegRep sigs
    pure (posSigs, negSigs)

resolveClassDeclaration :: CST.ClassDeclaration
                        -> ResolverM RST.ClassDeclaration
resolveClassDeclaration decl = do
  checkVarianceClassDeclaration decl.classdecl_loc decl.classdecl_kinds decl.classdecl_methods
  methodRes <- resolveMethods decl.classdecl_methods
  pure RST.MkClassDeclaration { classdecl_loc     = decl.classdecl_loc
                              , classdecl_doc     = decl.classdecl_doc
                              , classdecl_name    = decl.classdecl_name
                              , classdecl_kinds   = decl.classdecl_kinds
                              , classdecl_methods = methodRes
                              }

---------------------------------------------------------------------------------
-- Instance Declaration
---------------------------------------------------------------------------------

resolveInstanceDeclaration :: CST.InstanceDeclaration
                        -> ResolverM RST.InstanceDeclaration
resolveInstanceDeclaration decl = do
  typ <- resolveTyp PosRep decl.instancedecl_typ
  tyn <- resolveTyp NegRep decl.instancedecl_typ
  tc <- mapM resolveInstanceCase decl.instancedecl_cases
  pure RST.MkInstanceDeclaration { instancedecl_loc = decl.instancedecl_loc
                                 , instancedecl_doc = decl.instancedecl_doc
                                 , instancedecl_name = decl.instancedecl_name
                                 , instancedecl_class = decl.instancedecl_class
                                 , instancedecl_typ = (typ, tyn)
                                 , instancedecl_cases = tc
                                 }

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

resolveDecl :: CST.Declaration -> ResolverM RST.Declaration
resolveDecl (CST.PrdCnsDecl decl) = do
  case decl.pcdecl_pc of
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
  throwError (UnknownResolutionError defaultLoc "Unreachable: ParseErrorDecl cannot be parsed")

resolveModule :: CST.Module -> ResolverM RST.Module
resolveModule mod = do
  decls' <- mapM resolveDecl mod.mod_decls
  pure RST.MkModule { mod_name = mod.mod_name
                    , mod_libpath = mod.mod_libpath
                    , mod_decls = decls'
                    }
