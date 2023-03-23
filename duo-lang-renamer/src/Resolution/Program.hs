{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use mapM_" #-}
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
import Syntax.RST.Kinds
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
  mapM_ (checkVarianceXtor loc var' polyKind) xtorSigs
checkVarianceTyp loc var polyKind (CST.TyXRefined _loc' dataCodata  _tn xtorSigs) = do
  let var' = var <> case dataCodata of
                      CST.Data   -> Covariant
                      CST.Codata -> Contravariant
  mapM_ (checkVarianceXtor loc var' polyKind) xtorSigs
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
      mapM_ (\(_,_,ty) -> checkVarianceTyp loc var polyKind ty) tys'
checkVarianceTyp loc var polyKind (CST.TyBinOp _loc' ty _binOp ty') = do
  -- this might need to check whether only allowed binOps are used here (i.e. forbid data Union +a +b { Union(a \/ b) } )
  -- also, might need variance check
  checkVarianceTyp loc var polyKind ty
  checkVarianceTyp loc var polyKind ty'
checkVarianceTyp loc var polyKind (CST.TyParens _loc' ty) = checkVarianceTyp loc var polyKind ty
checkVarianceTyp loc var polyKind (CST.TyKindAnnot _ ty) = checkVarianceTyp loc var polyKind ty

checkVarianceXtor :: Loc -> Variance -> PolyKind -> CST.XtorSig -> ResolverM ()
checkVarianceXtor loc var polyKind xtor = do
  mapM_ f xtor.args
  where
    f :: CST.PrdCnsTyp -> ResolverM ()
    f (CST.PrdType ty) = checkVarianceTyp loc (Covariant     <> var) polyKind ty
    f (CST.CnsType ty) = checkVarianceTyp loc (Contravariant <> var) polyKind ty

checkVarianceDataDecl :: Loc -> PolyKind -> CST.DataCodata -> [CST.XtorSig] -> ResolverM ()
checkVarianceDataDecl loc polyKind pol xtors = do
  case pol of
    CST.Data   -> mapM_ (checkVarianceXtor loc Covariant     polyKind) xtors
    CST.Codata -> mapM_ (checkVarianceXtor loc Contravariant polyKind) xtors

resolveDataDecl :: CST.DataDecl -> ResolverM RST.DataDecl
resolveDataDecl decl = do
  case decl.isRefined of
    CST.NotRefined -> do
      -------------------------------------------------------------------------
      -- Nominal Data Type
      -------------------------------------------------------------------------
      NominalResult name' _ _ _ <- lookupTypeConstructor decl.loc decl.name
      -- Default the kind if none was specified:
      let polyKind = case decl.kind of
                        Nothing -> MkPolyKind [] (case decl.data_codata of CST.Data -> CBV; CST.Codata -> CBN)
                        Just knd -> knd
      checkVarianceDataDecl decl.loc polyKind decl.data_codata decl.xtors
      xtors' <- resolveXtors decl.xtors
      pure RST.NominalDecl { data_loc = decl.loc
                           , data_doc = decl.doc
                           , data_name = name'
                           , data_polarity = decl.data_codata
                           , data_kind = polyKind
                           , data_xtors = xtors'
                           }
    CST.Refined -> do
      -------------------------------------------------------------------------
      -- Refinement Data Type
      -------------------------------------------------------------------------
      NominalResult name' _ _ _ <- lookupTypeConstructor decl.loc decl.name
      -- Default the kind if none was specified:
      polyKind <- case decl.kind of
                        Nothing -> pure $ MkPolyKind [] (case decl.data_codata of CST.Data -> CBV; CST.Codata -> CBN)
                        Just knd -> pure knd
      checkVarianceDataDecl decl.loc polyKind decl.data_codata decl.xtors
      -- Lower the xtors in the adjusted environment (necessary for lowering xtors of refinement types)
      let g :: TypeNameResolve -> TypeNameResolve
          g (SynonymResult tn ty) = SynonymResult tn ty
          g (NominalResult tn dc _ polykind) = NominalResult tn dc CST.NotRefined polykind

          f :: Map ModuleName SymbolTable -> Map ModuleName SymbolTable
          f x = M.fromList (fmap (\(mn, st) -> (mn, st { typeNameMap = M.adjust g decl.name st.typeNameMap })) (M.toList x))

          h :: ResolveReader -> ResolveReader
          h r = r { rr_modules = f r.rr_modules }
      (xtorsPos, xtorsNeg) <- local h (resolveXtors decl.xtors)
      pure RST.RefinementDecl { data_loc = decl.loc
                              , data_doc = decl.doc
                              , data_name = name'
                              , data_polarity = decl.data_codata
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
  annot' <- resolveMaybeAnnot pcrep decl.annot
  term' <- resolveTerm pcrep decl.term
  pure $ RST.MkPrdCnsDeclaration { pcdecl_loc = decl.loc
                                 , pcdecl_doc = decl.doc
                                 , pcdecl_pc = pcrep
                                 , pcdecl_isRec = decl.isRecursive
                                 , pcdecl_name = decl.name
                                 , pcdecl_annot = annot'
                                 , pcdecl_term = term'
                                 }

---------------------------------------------------------------------------------
-- Command Declarations
---------------------------------------------------------------------------------

resolveCommandDeclaration :: CST.CommandDeclaration
                          -> ResolverM RST.CommandDeclaration
resolveCommandDeclaration decl = do
  cmd' <- resolveCommand decl.cmd
  pure $ RST.MkCommandDeclaration { cmddecl_loc = decl.loc
                                  , cmddecl_doc = decl.doc
                                  , cmddecl_name = decl.name
                                  , cmddecl_cmd = cmd'
                                  }

---------------------------------------------------------------------------------
-- Structural Xtor Declaration
---------------------------------------------------------------------------------

resolveStructuralXtorDeclaration :: CST.StructuralXtorDeclaration
                                 -> ResolverM RST.StructuralXtorDeclaration
resolveStructuralXtorDeclaration decl = do
  let evalOrder = case decl.evalOrder of
                  Just eo -> eo
                  Nothing -> case decl.data_codata of CST.Data -> CBV; CST.Codata -> CBN
  pure $ RST.MkStructuralXtorDeclaration { strxtordecl_loc = decl.loc
                                         , strxtordecl_doc = decl.doc
                                         , strxtordecl_xdata = decl.data_codata
                                         , strxtordecl_name = decl.name
                                         , strxtordecl_arity = decl.arity
                                         , strxtordecl_evalOrder = evalOrder
                                         }

---------------------------------------------------------------------------------
-- Type Operator Declaration
---------------------------------------------------------------------------------

resolveTyOpDeclaration :: CST.TyOpDeclaration
                       -> ResolverM RST.TyOpDeclaration
resolveTyOpDeclaration decl= do
  NominalResult tyname' _ _ _ <- lookupTypeConstructor decl.loc decl.res
  pure RST.MkTyOpDeclaration { tyopdecl_loc = decl.loc
                             , tyopdecl_doc = decl.doc
                             , tyopdecl_sym = decl.symbol
                             , tyopdecl_prec = decl.precedence
                             , tyopdecl_assoc = decl.associativity
                             , tyopdecl_res = tyname'
                             }

---------------------------------------------------------------------------------
-- Type Synonym Declaration
---------------------------------------------------------------------------------

resolveTySynDeclaration :: CST.TySynDeclaration
                        -> ResolverM RST.TySynDeclaration
resolveTySynDeclaration decl = do
  typ <- resolveTyp PosRep decl.res
  tyn <- resolveTyp NegRep decl.res
  pure RST.MkTySynDeclaration { tysyndecl_loc = decl.loc
                              , tysyndecl_doc = decl.doc
                              , tysyndecl_name = decl.name
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
  checkVarianceClassDeclaration decl.loc decl.kinds decl.methods
  methodRes <- resolveMethods decl.methods
  pure RST.MkClassDeclaration { classdecl_loc     = decl.loc
                              , classdecl_doc     = decl.doc
                              , classdecl_name    = decl.name
                              , classdecl_kinds   = decl.kinds
                              , classdecl_methods = methodRes
                              }

---------------------------------------------------------------------------------
-- Instance Declaration
---------------------------------------------------------------------------------

resolveInstanceDeclaration :: CST.InstanceDeclaration
                        -> ResolverM RST.InstanceDeclaration
resolveInstanceDeclaration decl = do
  typ <- resolveTyp PosRep decl.typ
  tyn <- resolveTyp NegRep decl.typ
  tc <- mapM resolveInstanceCase decl.cases
  pure RST.MkInstanceDeclaration { instancedecl_loc = decl.loc
                                 , instancedecl_doc = decl.doc
                                 , instancedecl_name = decl.instance_name
                                 , instancedecl_class = decl.class_name
                                 , instancedecl_typ = (typ, tyn)
                                 , instancedecl_cases = tc
                                 }

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

resolveDecl :: CST.Declaration -> ResolverM RST.Declaration
resolveDecl (CST.PrdCnsDecl decl) = do
  case decl.prd_cns of
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
  decls' <- mapM resolveDecl mod.decls
  pure RST.MkModule { mod_name = mod.name
                    , mod_libpath = mod.libpath
                    , mod_decls = decls'
                    }
