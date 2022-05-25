module Resolution.Program (renameProgram, renameDecl) where

import Control.Monad.Reader
import Control.Monad.Except (throwError)
import Data.Map (Map)
import Data.Map qualified as M

import Errors
import Resolution.Definition
import Resolution.SymbolTable
import Resolution.Terms (renameTerm, renameCommand)
import Resolution.Types (renameTypeScheme, renameXTorSig, renameTyp)
import Syntax.CST.Program qualified as CST
import Syntax.Common.TypesUnpol qualified as CST
import Syntax.RST.Program qualified as RST
import Syntax.Common.TypesPol qualified as RST
import Syntax.Common
import Utils (Loc)

renameXtors :: [CST.XtorSig]
           -> RenamerM ([RST.XtorSig Pos], [RST.XtorSig Neg])
renameXtors sigs = do
    posSigs <- sequence $ renameXTorSig PosRep <$> sigs
    negSigs <- sequence $ renameXTorSig NegRep <$> sigs
    pure (posSigs, negSigs)

renameDataDecl :: Loc -> CST.DataDecl -> RenamerM RST.DataDecl
renameDataDecl loc CST.NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors } = do
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
  xtors <- local f (renameXtors data_xtors)
  -- Create the new data declaration
  let dcl = RST.NominalDecl
                { data_refined = data_refined
                , data_name = data_name'
                , data_polarity = data_polarity
                , data_kind = polyKind
                , data_xtors = xtors
                }
  pure dcl

renameAnnot :: PrdCnsRep pc -> CST.TypeScheme -> RenamerM (RST.TypeScheme (PrdCnsToPol pc))
renameAnnot PrdRep ts = renameTypeScheme PosRep ts
renameAnnot CnsRep ts = renameTypeScheme NegRep ts

renameMaybeAnnot :: PrdCnsRep pc -> Maybe (CST.TypeScheme) -> RenamerM (Maybe (RST.TypeScheme (PrdCnsToPol pc)))
renameMaybeAnnot _ Nothing = pure Nothing
renameMaybeAnnot pc (Just annot) = Just <$> renameAnnot pc annot

renameDecl :: CST.Declaration -> RenamerM RST.Declaration
renameDecl (CST.PrdCnsDecl loc doc Prd isrec fv annot tm) =
  RST.PrdCnsDecl loc doc PrdRep isrec fv <$> (renameMaybeAnnot PrdRep annot) <*> (renameTerm PrdRep tm)
renameDecl (CST.PrdCnsDecl loc doc Cns isrec fv annot tm) =
  RST.PrdCnsDecl loc doc CnsRep isrec fv <$> (renameMaybeAnnot CnsRep annot) <*> (renameTerm CnsRep tm)
renameDecl (CST.CmdDecl loc doc fv cmd) =
  RST.CmdDecl loc doc fv <$> (renameCommand cmd)
renameDecl (CST.DataDecl loc doc dd) = do
  lowered <- renameDataDecl loc dd
  pure $ RST.DataDecl loc doc lowered
renameDecl (CST.XtorDecl loc doc dc xt args ret) = do
  let ret' = case ret of
               Just eo -> eo
               Nothing -> case dc of Data -> CBV; Codata -> CBN
  pure $ RST.XtorDecl loc doc dc xt args ret'
renameDecl (CST.ImportDecl loc doc mod) = do
  pure $ RST.ImportDecl loc doc mod
renameDecl (CST.SetDecl loc doc txt) =
  pure $ RST.SetDecl loc doc txt
renameDecl (CST.TyOpDecl loc doc op prec assoc tyname) = do
  NominalResult tyname' _ _ _ <- lookupTypeConstructor loc tyname
  pure $ RST.TyOpDecl loc doc op prec assoc tyname'
renameDecl (CST.TySynDecl loc doc nm ty) = do
  typ <- renameTyp PosRep ty
  tyn <- renameTyp NegRep ty
  pure (RST.TySynDecl loc doc nm (typ, tyn))
renameDecl CST.ParseErrorDecl =
  throwError (OtherError Nothing "Unreachable: ParseErrorDecl cannot be parsed")

renameProgram :: CST.Program -> RenamerM RST.Program
renameProgram = sequence . fmap renameDecl
