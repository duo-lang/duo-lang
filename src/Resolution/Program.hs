module Resolution.Program (resolveProgram, resolveDecl) where

import Control.Monad.Reader
import Control.Monad.Except (throwError)
import Data.Map (Map)
import Data.Map qualified as M

import Errors
import Resolution.Definition
import Resolution.SymbolTable
import Resolution.Terms (resolveTerm, resolveCommand)
import Resolution.Types (resolveTypeScheme, resolveXTorSig, resolveTyp)
import Syntax.CST.Program qualified as CST
import Syntax.Common.TypesUnpol qualified as CST
import Syntax.RST.Program qualified as RST
import Syntax.Common.TypesPol qualified as RST
import Syntax.Common
import Utils (Loc)

---------------------------------------------------------------------------------
-- Data Declarations
---------------------------------------------------------------------------------

resolveXtors :: [CST.XtorSig]
           -> ResolverM ([RST.XtorSig Pos], [RST.XtorSig Neg])
resolveXtors sigs = do
    posSigs <- sequence $ resolveXTorSig PosRep <$> sigs
    negSigs <- sequence $ resolveXTorSig NegRep <$> sigs
    pure (posSigs, negSigs)

resolveDataDecl :: Loc -> CST.DataDecl -> ResolverM RST.DataDecl
resolveDataDecl loc CST.NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors } = do
  NominalResult data_name' _ _ _ <- lookupTypeConstructor loc data_name
  -- Default the kind if none was specified:
  let polyKind = case data_kind of
                    Nothing -> MkPolyKind [] (case data_polarity of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
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
resolveDecl (CST.DataDecl loc doc dd) = do
  lowered <- resolveDataDecl loc dd
  pure $ RST.DataDecl loc doc lowered
resolveDecl (CST.XtorDecl decl) = do
  decl' <- resolveStructuralXtorDeclaration decl
  pure $ RST.XtorDecl decl'
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
