module Renamer.Program (renameProgram, renameDecl) where

import Control.Monad.Except (throwError)
import Control.Monad.State
import Data.Map qualified as M
import Data.Text.IO qualified as T

import Errors
import Renamer.Definition
import Renamer.SymbolTable
import Renamer.Terms (renameTerm, renameCommand)
import Renamer.Types (renameTypeScheme, renameXTorSig, renameTyp)
import Parser.Parser ( runFileParser, programP )
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.Common
import Utils (Loc)

renameXtors :: [CST.XtorSig]
           -> RenamerM ([RST.XtorSig Pos], [RST.XtorSig Neg])
renameXtors sigs = do
    posSigs <- sequence $ renameXTorSig PosRep <$> sigs
    negSigs <- sequence $ renameXTorSig NegRep <$> sigs
    pure (posSigs, negSigs)

renameDataDecl :: Loc -> CST.DataDecl -> RenamerM RST.DataDecl
renameDataDecl _ CST.NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors } = do
  -- Default the kind if none was specified:
  let polyKind = case data_kind of
                    Nothing -> MkPolyKind [] (case data_polarity of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
  -- Insert the tycon arity into the environment
  updateSymbolTable (\st -> st { tyConMap = M.insert data_name (NominalResult data_refined polyKind) (tyConMap st)})
  -- Lower the xtors
  xtors <- renameXtors data_xtors
  let ns = case data_refined of
                  Refined -> Refinement
                  NotRefined -> Nominal
  -- Create the new data declaration
  let dcl = RST.NominalDecl
                { data_refined = data_refined
                , data_name = data_name
                , data_polarity = data_polarity
                , data_kind = polyKind
                , data_xtors = xtors
                }
  -- Insert the xtors into the environment
  let newXtors = (M.fromList [((RST.sig_name xt,data_polarity), (ns, RST.linearContextToArity (RST.sig_args xt)))| xt <- fst xtors])
  updateSymbolTable (\st -> st { xtorMap = M.union newXtors (xtorMap st)})
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

  let ns = case CST.data_refined dd of
                 Refined -> Refinement
                 NotRefined -> Nominal
  let newXtors = M.fromList [((RST.sig_name xt, CST.data_polarity dd), (ns, RST.linearContextToArity (RST.sig_args xt)))| xt <- fst (RST.data_xtors lowered)]
  updateSymbolTable (\st -> st { xtorMap = M.union newXtors (xtorMap st)})
  pure $ RST.DataDecl loc doc lowered
renameDecl (CST.XtorDecl loc doc dc xt args ret) = do
  updateSymbolTable (\st -> st { xtorMap = M.insert (xt,dc) (Structural, fst <$> args) (xtorMap st)})
  let ret' = case ret of
               Just eo -> eo
               Nothing -> case dc of Data -> CBV; Codata -> CBN
  pure $ RST.XtorDecl loc doc dc xt args ret'
renameDecl (CST.ImportDecl loc doc mod) = do
  fp <- findModule mod loc
  newSymbolTable <- renameProgramFromDisk fp
  updateSymbolTable (\st -> st <> newSymbolTable)
  pure $ RST.ImportDecl loc doc mod
renameDecl (CST.SetDecl loc doc txt) =
  pure $ RST.SetDecl loc doc txt
renameDecl (CST.TyOpDecl loc doc op prec assoc tyname) = do
  let tyOp = MkTyOp { symbol = CustomOp op
                    , prec = prec
                    , assoc = assoc
                    , desugar = NominalDesugaring tyname
                    }
  updateSymbolTable (\st -> st { tyOps = tyOp : (tyOps st)})
  pure $ RST.TyOpDecl loc doc op prec assoc tyname
renameDecl (CST.TySynDecl loc doc nm ty) = do
  typ <- renameTyp PosRep ty
  tyn <- renameTyp NegRep ty
  updateSymbolTable (\st -> st { tyConMap = M.insert nm (SynonymResult ty) (tyConMap st)})
  pure (RST.TySynDecl loc doc nm (typ, tyn))
renameDecl CST.ParseErrorDecl =
  throwError (OtherError Nothing "Unreachable: ParseErrorDecl cannot be parsed")

renameProgram :: CST.Program -> RenamerM RST.Program
renameProgram = sequence . fmap renameDecl

renameProgramFromDisk :: FilePath
                     -> RenamerM SymbolTable
renameProgramFromDisk fp = do
  file <- liftIO $ T.readFile fp
  decls <- runFileParser fp programP file
  pure $ createSymbolTable decls