module Renamer.Program (lowerProgram, lowerDecl) where

import Control.Monad.Except (throwError)
import Control.Monad.State
import Data.Map qualified as M
import Data.Text.IO qualified as T

import Errors
import Renamer.Definition
import Renamer.SymbolTable
import Renamer.Terms (lowerTerm, lowerCommand)
import Renamer.Types (lowerTypeScheme, lowerXTorSig)
import Parser.Parser ( runFileParser, programP )
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.AST.Program qualified as AST
import Syntax.AST.Types qualified as AST
import Syntax.Common
import Utils (Loc)

lowerXtors :: [CST.XtorSig]
           -> RenamerM ([AST.XtorSig Pos], [AST.XtorSig Neg])
lowerXtors sigs = do
    posSigs <- sequence $ lowerXTorSig PosRep <$> sigs
    negSigs <- sequence $ lowerXTorSig NegRep <$> sigs
    pure (posSigs, negSigs)

lowerDataDecl :: Loc -> CST.DataDecl -> RenamerM AST.DataDecl
lowerDataDecl _ CST.NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors } = do
  -- Default the kind if none was specified:
  let polyKind = case data_kind of
                    Nothing -> MkPolyKind [] [] (case data_polarity of Data -> CBV; Codata -> CBN)
                    Just knd -> knd
  -- Insert the tycon arity into the environment
  updateSymbolTable (\st -> st { tyConMap = M.insert data_name (data_refined, polyKind) (tyConMap st)})
  -- Lower the xtors
  xtors <- lowerXtors data_xtors
  let ns = case data_refined of
                  Refined -> Refinement
                  NotRefined -> Nominal
  -- Create the new data declaration
  let dcl = AST.NominalDecl
                { data_refined = data_refined
                , data_name = data_name
                , data_polarity = data_polarity
                , data_kind = polyKind
                , data_xtors = xtors
                }
  -- Insert the xtors into the environment
  let newXtors = (M.fromList [((AST.sig_name xt,data_polarity), (ns, AST.linearContextToArity (AST.sig_args xt)))| xt <- fst xtors])
  updateSymbolTable (\st -> st { xtorMap = M.union newXtors (xtorMap st)})
  pure dcl

lowerAnnot :: PrdCnsRep pc -> CST.TypeScheme -> RenamerM (AST.TypeScheme (PrdCnsToPol pc))
lowerAnnot PrdRep ts = lowerTypeScheme PosRep ts
lowerAnnot CnsRep ts = lowerTypeScheme NegRep ts

lowerMaybeAnnot :: PrdCnsRep pc -> Maybe (CST.TypeScheme) -> RenamerM (Maybe (AST.TypeScheme (PrdCnsToPol pc)))
lowerMaybeAnnot _ Nothing = pure Nothing
lowerMaybeAnnot pc (Just annot) = Just <$> lowerAnnot pc annot

lowerDecl :: CST.Declaration -> RenamerM AST.Declaration
lowerDecl (CST.PrdCnsDecl doc loc Prd isrec fv annot tm) =
  AST.PrdCnsDecl (doc, loc) PrdRep isrec fv <$> (lowerMaybeAnnot PrdRep annot) <*> (lowerTerm PrdRep tm)
lowerDecl (CST.PrdCnsDecl doc loc Cns isrec fv annot tm) =
  AST.PrdCnsDecl (doc, loc) CnsRep isrec fv <$> (lowerMaybeAnnot CnsRep annot) <*> (lowerTerm CnsRep tm)
lowerDecl (CST.CmdDecl doc loc fv cmd) =
  AST.CmdDecl (doc, loc) fv <$> (lowerCommand cmd)
lowerDecl (CST.DataDecl doc loc dd) = do
  lowered <- lowerDataDecl loc dd

  let ns = case CST.data_refined dd of
                 Refined -> Refinement
                 NotRefined -> Nominal
  let newXtors = M.fromList [((AST.sig_name xt, CST.data_polarity dd), (ns, AST.linearContextToArity (AST.sig_args xt)))| xt <- fst (AST.data_xtors lowered)]
  updateSymbolTable (\st -> st { xtorMap = M.union newXtors (xtorMap st)})
  pure $ AST.DataDecl (doc,loc) lowered
lowerDecl (CST.XtorDecl doc loc dc xt args ret) = do
  updateSymbolTable (\st -> st { xtorMap = M.insert (xt,dc) (Structural, fst <$> args) (xtorMap st)})
  let ret' = case ret of
               Just eo -> eo
               Nothing -> case dc of Data -> CBV; Codata -> CBN
  pure $ AST.XtorDecl (doc, loc) dc xt args ret'
lowerDecl (CST.ImportDecl doc loc mod) = do
  fp <- findModule mod loc
  newSymbolTable <- lowerProgramFromDisk fp
  updateSymbolTable (\st -> st <> newSymbolTable)
  pure $ AST.ImportDecl (doc, loc) mod
lowerDecl (CST.SetDecl doc loc txt) =
  pure $ AST.SetDecl (doc, loc) txt
lowerDecl (CST.TyOpDecl doc loc op prec assoc tyname) = do
  let tyOp = MkTyOp { symbol = CustomOp op
                    , prec = prec
                    , assoc = assoc
                    , desugar = NominalDesugaring tyname
                    }
  updateSymbolTable (\st -> st { tyOps = tyOp : (tyOps st)})
  pure $ AST.TyOpDecl (doc, loc) op prec assoc tyname
lowerDecl CST.ParseErrorDecl =
  throwError (OtherError Nothing "Unreachable: ParseErrorDecl cannot be parsed")

lowerProgram :: CST.Program -> RenamerM AST.Program
lowerProgram = sequence . fmap lowerDecl

lowerProgramFromDisk :: FilePath
                     -> RenamerM SymbolTable
lowerProgramFromDisk fp = do
  file <- liftIO $ T.readFile fp
  decls <- runFileParser fp programP file
  pure $ createSymbolTable decls