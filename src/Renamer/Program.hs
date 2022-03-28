module Renamer.Program (lowerProgram, lowerDecl) where

import Control.Monad.Except (throwError)
import Control.Monad.State
import Data.Map qualified as M
import Data.Text.IO qualified as T

import Driver.Definition
import Driver.Environment (Environment(..))
import Errors
import Renamer.Terms (lowerTerm, lowerCommand)
import Renamer.Types (lowerTypeScheme, lowerXTorSig)
import Parser.Parser ( runFileParser, programP )
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.AST.Program qualified as AST
import Syntax.AST.Types qualified as AST
import Syntax.Common
import Utils (Loc)



lowerXtors :: [CST.XtorSig] -> DriverM ([AST.XtorSig Pos], [AST.XtorSig Neg])
lowerXtors sigs = do
    posSigs <- sequence $ lowerXTorSig PosRep <$> sigs
    negSigs <- sequence $ lowerXTorSig NegRep <$> sigs
    pure (posSigs, negSigs)

lowerDataDecl :: Loc -> CST.DataDecl -> DriverM AST.DataDecl
lowerDataDecl loc CST.NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors } = do
  -- HACK: Insert preliminary data declaration information (needed to lower type constructor applications)
  env <- gets driverEnv
  let prelim_dd = AST.NominalDecl
        { data_refined = data_refined
        , data_name = data_name
        , data_polarity = data_polarity
        , data_kind = case data_kind of
            Nothing -> MkPolyKind [] [] (case data_polarity of Data -> CBV; Codata -> CBN)
            Just knd -> knd
        , data_xtors = ([], [])
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
  let newEnv = env { declEnv = (loc, dcl) : prevDeclEnv
                   , xtorMap = M.union (M.fromList [((AST.sig_name xt,data_polarity), (ns, AST.linearContextToArity (AST.sig_args xt)))| xt <- fst (AST.data_xtors dcl)]) (xtorMap env)}
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
  let newEnv = env { xtorMap = M.union (M.fromList [((AST.sig_name xt, CST.data_polarity dd), (ns, AST.linearContextToArity (AST.sig_args xt)))| xt <- fst (AST.data_xtors lowered)]) (xtorMap env)}
  setEnvironment newEnv
  pure $ AST.DataDecl loc lowered
lowerDecl (CST.XtorDecl loc dc xt args ret) = do
  env <- gets driverEnv
  let newEnv = env { xtorMap = M.insert (xt,dc) (Structural, fst <$> args) (xtorMap env)}
  setEnvironment newEnv
  let ret' = case ret of
               Just eo -> eo
               Nothing -> case dc of Data -> CBV; Codata -> CBN
  pure $ AST.XtorDecl loc dc xt args ret'
lowerDecl (CST.ImportDecl loc mod) = do
  fp <- findModule mod loc
  oldEnv <- gets driverEnv
  newEnv <- lowerProgramFromDisk fp
  setEnvironment (oldEnv <> newEnv)
  pure $ AST.ImportDecl loc mod
lowerDecl (CST.SetDecl loc txt)             = pure $ AST.SetDecl loc txt
lowerDecl (CST.TyOpDecl loc op prec assoc tyname) = pure $ AST.TyOpDecl loc op prec assoc tyname
lowerDecl CST.ParseErrorDecl                = throwError (OtherError Nothing "Unreachable: ParseErrorDecl cannot be parsed")

lowerProgram :: CST.Program -> DriverM (AST.Program Parsed)
lowerProgram = sequence . fmap lowerDecl


createSymbolTable :: CST.Program  -> Environment Inferred
createSymbolTable [] = mempty
createSymbolTable ((CST.XtorDecl _ dc xt args _):decls) =
  let x = createSymbolTable decls
  in x { xtorMap = M.insert (xt,dc) (Structural, fst <$> args) (xtorMap x)}
createSymbolTable ((CST.DataDecl loc dd):decls) =
  let ns = case CST.data_refined dd of
               Refined -> Refinement
               NotRefined -> Nominal
      x = createSymbolTable decls
      xtors = M.fromList [((CST.sig_name xt, CST.data_polarity dd), (ns, CST.linearContextToArity (CST.sig_args xt)))| xt <- CST.data_xtors dd]
  -- HACK: The type parameter arities of imported types need to be known in lowering,
  -- hence we add a partial AST.NominalDecl without constructors for now
  in x { declEnv = (loc, AST.NominalDecl
        { data_refined = CST.data_refined dd
        , data_name = CST.data_name dd
        , data_polarity = CST.data_polarity dd
        , data_kind = case CST.data_kind dd of
          Nothing -> MkPolyKind [] [] (case CST.data_polarity dd of { Data -> CBV; Codata -> CBN })
          Just knd -> knd
        , data_xtors = ([], [])
        }) : declEnv x,
         xtorMap  = M.union xtors (xtorMap x)}
createSymbolTable (_:decls) = createSymbolTable decls


lowerProgramFromDisk :: FilePath
                     -> DriverM (Environment Inferred)
lowerProgramFromDisk fp = do
  file <- liftIO $ T.readFile fp
  decls <- runFileParser fp programP file
  pure $ createSymbolTable decls