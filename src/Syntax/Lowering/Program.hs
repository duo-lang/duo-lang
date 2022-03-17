module Syntax.Lowering.Program (lowerProgram, lowerDecl) where

import Control.Monad.Except (throwError)
import Control.Monad.State
import Data.Map qualified as M

import Errors
import Syntax.Lowering.Terms (lowerTerm, lowerCommand)
import Syntax.Lowering.Types (lowerTypeScheme, lowerXTorSig)
import Driver.Definition
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.AST.Program qualified as AST
import Syntax.AST.Types qualified as AST
import Syntax.Common
import Syntax.Environment (Environment(..))
import Driver.SymbolTable (SymbolTable(..), createSymbolTableFromDisk)
import Syntax.AST.Types (DataDecl(data_params))
import Utils (Loc)



lowerXtors :: [CST.XtorSig] -> DriverM ([AST.XtorSig Pos], [AST.XtorSig Neg])
lowerXtors sigs = do
    posSigs <- sequence $ lowerXTorSig PosRep <$> sigs
    negSigs <- sequence $ lowerXTorSig NegRep <$> sigs
    pure (posSigs, negSigs)

lowerDataDecl :: Loc -> CST.DataDecl -> DriverM AST.DataDecl
lowerDataDecl loc CST.NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors, data_params } = do
  -- HACK: Insert preliminary data declaration information (needed to lower type constructor applications)
  env <- gets driverEnv
  let prelim_dd = AST.NominalDecl
        { data_refined = data_refined
        , data_name = data_name
        , data_polarity = data_polarity
        , data_kind = data_kind
        , data_xtors = ([], [])
        , data_params = data_params
        }

  let prevDeclEnv = declEnv env
  let newEnv = env { declEnv = (loc, prelim_dd) : declEnv env }
  setEnvironment newEnv

  xtors <- lowerXtors data_xtors

  let ns = case data_refined of
                  Refined -> Refinement
                  NotRefined -> Nominal

  -- HACK: insert final data declaration into environment
  let dcl = prelim_dd { AST.data_xtors = xtors}
  let newXtors = (M.fromList [((AST.sig_name xt,data_polarity), (ns, AST.linearContextToArity (AST.sig_args xt)))| xt <- fst (AST.data_xtors dcl)])
  let newSymTable = MkSymbolTable (M.union newXtors (xtorMap (symTable env))) (tyConMap (symTable env))
  let newEnv = env { declEnv = (loc, dcl) : prevDeclEnv
                   , symTable = newSymTable }
  setEnvironment newEnv

  pure dcl

lowerAnnot :: PrdCnsRep pc -> CST.TypeScheme -> DriverM (AST.TypeScheme (PrdCnsToPol pc))
lowerAnnot PrdRep ts = lowerTypeScheme PosRep ts
lowerAnnot CnsRep ts = lowerTypeScheme NegRep ts

lowerMaybeAnnot :: PrdCnsRep pc -> Maybe (CST.TypeScheme) -> DriverM (Maybe (AST.TypeScheme (PrdCnsToPol pc)))
lowerMaybeAnnot _ Nothing = pure Nothing
lowerMaybeAnnot pc (Just annot) = Just <$> lowerAnnot pc annot

lowerDecl :: CST.Declaration -> DriverM (AST.Declaration Parsed)
lowerDecl (CST.PrdCnsDecl loc Prd isrec fv annot tm) = AST.PrdCnsDecl loc PrdRep isrec fv <$> (lowerMaybeAnnot PrdRep annot) <*> (lowerTerm PrdRep tm)
lowerDecl (CST.PrdCnsDecl loc Cns isrec fv annot tm) = AST.PrdCnsDecl loc CnsRep isrec fv <$> (lowerMaybeAnnot CnsRep annot) <*> (lowerTerm CnsRep tm)
lowerDecl (CST.CmdDecl loc fv cmd)          = AST.CmdDecl loc fv <$> (lowerCommand cmd)
lowerDecl (CST.DataDecl loc dd)             = do
  lowered <- lowerDataDecl loc dd
  env <- gets driverEnv
  let ns = case CST.data_refined dd of
                 Refined -> Refinement
                 NotRefined -> Nominal
  let newXtors = (M.fromList [((AST.sig_name xt, CST.data_polarity dd), (ns, AST.linearContextToArity (AST.sig_args xt)))| xt <- fst (AST.data_xtors lowered)])
  let newSymTable = MkSymbolTable (M.union newXtors (xtorMap (symTable env))) (tyConMap (symTable env))
  let newEnv = env { symTable =  newSymTable }
  setEnvironment newEnv
  pure $ AST.DataDecl loc lowered
lowerDecl (CST.XtorDecl loc dc xt args ret) = do
  env <- gets driverEnv
  let newSymTable = MkSymbolTable (M.insert (xt,dc) (Structural, fst <$> args) (xtorMap (symTable env))) (tyConMap (symTable env))
  let newEnv = env { symTable = newSymTable }
  setEnvironment newEnv
  pure $ AST.XtorDecl loc dc xt args ret
lowerDecl (CST.ImportDecl loc mod) = do
  fp <- findModule mod loc
  oldEnv <- gets driverEnv
  newEnv <- createSymbolTableFromDisk fp
  setEnvironment (oldEnv <> mempty { symTable = newEnv })
  pure $ AST.ImportDecl loc mod
lowerDecl (CST.SetDecl loc txt)             = pure $ AST.SetDecl loc txt
lowerDecl CST.ParseErrorDecl                = throwError (OtherError Nothing "Unreachable: ParseErrorDecl cannot be parsed")

lowerProgram :: CST.Program -> DriverM (AST.Program Parsed)
lowerProgram = sequence . fmap lowerDecl