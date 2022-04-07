module Driver.Driver
  ( InferenceOptions(..)
  , defaultInferenceOptions
  , DriverState(..)
  , execDriverM
  , inferProgramIO
  , inferProgramIO'
  , renameProgramIO
  , inferDecl
  ) where

import Control.Monad.State
import Control.Monad.Except
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Text.IO qualified as T

import Driver.Definition
import Driver.Environment 
import Errors
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint, ppPrintIO )
import Renamer.Program (lowerProgram)
import Renamer.SymbolTable

import Syntax.Common
import Syntax.CST.Program qualified as CST
import Syntax.AST.Program qualified as AST
import Syntax.AST.Terms qualified as AST
import Syntax.RST.Types qualified as RST
import Syntax.RST.Program qualified as RST
import TypeAutomata.Simplify
import TypeAutomata.Subsume (subsume)
import TypeInference.Coalescing ( coalesce )
import TypeInference.GenerateConstraints.Definition
    ( runGenM )
import TypeInference.GenerateConstraints.Terms
    ( genConstraintsTerm,
      genConstraintsCommand,
      genConstraintsTermRecursive )
import TypeInference.SolveConstraints (solveConstraints)
import Utils ( Loc )
import Data.List

checkAnnot :: PolarityRep pol
           -> RST.TypeScheme pol -- ^ Inferred type
           -> Maybe (RST.TypeScheme pol) -- ^ Annotated type
           -> Loc -- ^ Location for the error message
           -> DriverM (RST.TypeScheme pol)
checkAnnot _ tyInferred Nothing _ = return tyInferred
checkAnnot rep tyInferred (Just tyAnnotated) loc = do
  let isSubsumed = subsume rep tyInferred tyAnnotated
  case isSubsumed of
      (Left err) -> throwError (attachLoc loc err)
      (Right True) -> return tyAnnotated
      (Right False) -> do
        let err = OtherError (Just loc) $ T.unlines [ "Annotated type is not subsumed by inferred type"
                                                    , " Annotated type: " <> ppPrint tyAnnotated
                                                    , " Inferred type:  " <> ppPrint tyInferred
                                                    ]
        guardVerbose $ ppPrintIO err
        throwError err

---------------------------------------------------------------------------------
-- Infer Declarations
---------------------------------------------------------------------------------

inferDecl :: RST.Declaration
           -> DriverM AST.Declaration
--
-- PrdCnsDecl
--
inferDecl (RST.PrdCnsDecl loc doc pc isRec fv annot term) = do
  infopts <- gets driverOpts
  env <- gets driverEnv
  -- 1. Generate the constraints.
  let genFun = case isRec of
        Recursive -> genConstraintsTermRecursive loc fv pc term
        NonRecursive -> genConstraintsTerm term
  (tmInferred, constraintSet) <- liftEitherErr loc $ runGenM env genFun
  guardVerbose $ ppPrintIO constraintSet
  -- 2. Solve the constraints.
  solverResult <- liftEitherErr loc $ solveConstraints constraintSet env
  guardVerbose $ ppPrintIO solverResult
  -- 3. Coalesce the result
  let bisubst = coalesce solverResult
  guardVerbose $ ppPrintIO bisubst
  -- 4. Read of the type and generate the resulting type
  let typ = RST.zonk bisubst (AST.getTypeTerm tmInferred)
  guardVerbose $ putStr "\nInferred type: " >> ppPrintIO typ >> putStrLn ""
  -- 5. Simplify
  typSimplified <- case infOptsSimplify infopts of
    True -> do
      printGraphs <- gets (infOptsPrintGraphs . driverOpts)
      tys <- simplify (RST.generalize typ) printGraphs (T.unpack (unFreeVarName fv))
      guardVerbose $ putStr "\nInferred type (Simplified): " >> ppPrintIO tys >> putStrLn ""
      return tys
    False -> return (RST.generalize typ)
  -- 6. Check type annotation.
  ty <- checkAnnot (prdCnsToPol pc) typSimplified annot loc
  -- 7. Insert into environment
  env <- gets driverEnv
  case pc of
    PrdRep -> do
      let newEnv = env { prdEnv  = M.insert fv (tmInferred ,loc, ty) (prdEnv env) }
      setEnvironment newEnv
      return (AST.PrdCnsDecl loc doc pc isRec fv (Just ty) tmInferred)
    CnsRep -> do
      let newEnv = env { cnsEnv  = M.insert fv (tmInferred, loc, ty) (cnsEnv env) }
      setEnvironment newEnv
      return (AST.PrdCnsDecl loc doc pc isRec fv (Just ty) tmInferred)
--
-- CmdDecl
--
inferDecl (RST.CmdDecl loc doc v cmd) = do
  env <- gets driverEnv
  -- Generate the constraints
  (cmdInferred,constraints) <- liftEitherErr loc $ runGenM env (genConstraintsCommand cmd)
  -- Solve the constraints
  solverResult <- liftEitherErr loc $ solveConstraints constraints env
  guardVerbose $ do
      ppPrintIO constraints
      ppPrintIO solverResult
  -- Insert into environment
  env <- gets driverEnv
  let newEnv = env { cmdEnv  = M.insert v (cmdInferred, loc) (cmdEnv env)}
  setEnvironment newEnv
  return (AST.CmdDecl loc doc v cmdInferred)
--
-- DataDecl
--
inferDecl (RST.DataDecl loc doc dcl) = do
  -- Insert into environment
  env <- gets driverEnv
  st <- gets driverSymbols
  let tn = RST.data_name dcl
  case find (\RST.NominalDecl{..} -> data_name == tn) (snd <$> declEnv env) of
    Just _ ->
        -- HACK: inserting in the environment has already been done in lowering
        -- because the declarations are already needed for lowering
        -- In that case we make sure we don't insert twice
        return (AST.DataDecl loc doc dcl)
    Nothing -> do
      let ns = case RST.data_refined dcl of
                      Refined -> Refinement
                      NotRefined -> Nominal
      let newXtors = M.fromList [((RST.sig_name xt, RST.data_polarity dcl), (ns,RST.linearContextToArity (RST.sig_args xt)))| xt <- fst (RST.data_xtors dcl)]
      let newEnv = env { declEnv = (loc,dcl) : declEnv env }
      let newSt  = st { xtorMap = M.union  newXtors (xtorMap st) }
      setEnvironment newEnv
      setSymboltable newSt
      return (AST.DataDecl loc doc dcl)
--
-- XtorDecl
--
inferDecl (RST.XtorDecl loc doc dc xt args ret) = do
  symbolTable <- gets driverSymbols
  let newSymbolTable = symbolTable { xtorMap = M.insert (xt,dc) (Structural, fst <$> args) (xtorMap symbolTable) }
  setSymboltable newSymbolTable
  pure $ AST.XtorDecl loc doc dc xt args ret
--
-- ImportDecl
--
inferDecl (RST.ImportDecl loc doc mod) = do
  fp <- findModule mod loc
  oldEnv <- gets driverEnv
  newEnv <- fst <$> inferProgramFromDisk fp
  setEnvironment (oldEnv <> newEnv)
  return (AST.ImportDecl loc doc mod)
--
-- SetDecl
--
inferDecl (RST.SetDecl _ _ txt) = case T.unpack txt of
  _ -> throwOtherError ["Unknown option: " <> txt]
--
-- TyOpDecl
--
inferDecl (RST.TyOpDecl loc doc op prec assoc ty) = do
  pure (AST.TyOpDecl loc doc op prec assoc ty)

---------------------------------------------------------------------------------
-- Infer programs
---------------------------------------------------------------------------------

inferProgramFromDisk :: FilePath
                     -> DriverM (Environment, AST.Program)
inferProgramFromDisk fp = do
  file <- liftIO $ T.readFile fp
  decls <- runFileParser fp programP file
  -- Use inference options of parent? Probably not?
  x <- liftIO $ inferProgramIO  (DriverState defaultInferenceOptions { infOptsLibPath = ["examples"] } mempty mempty) decls
  case x of
     Left err -> throwError err
     Right env -> return env

inferProgram :: [CST.Declaration]
             -> DriverM AST.Program
inferProgram decls = do
  decls <- renameProgram decls
  forM decls inferDecl

renameProgram :: [CST.Declaration]
              -> DriverM RST.Program
renameProgram decls = lowerProgram decls

renameProgramIO :: DriverState
                -> [CST.Declaration]
                -> IO (Either Error RST.Program)
renameProgramIO state decls = do
  x <- execDriverM state (renameProgram decls)
  case x of
      Left err -> return (Left err)
      Right (res,_) -> return (Right res)

inferProgram' :: RST.Program
              -> DriverM AST.Program
inferProgram' decls = forM decls inferDecl

inferProgramIO  :: DriverState -- ^ Initial State
                -> [CST.Declaration]
                -> IO (Either Error (Environment, AST.Program))
inferProgramIO state decls = do
  x <- execDriverM state (inferProgram decls)
  case x of
      Left err -> return (Left err)
      Right (res,x) -> return (Right ((driverEnv x), res))

inferProgramIO' :: DriverState -- ^ Initial State
                -> RST.Program
                -> IO (Either Error (Environment, AST.Program))
inferProgramIO' state decls = do
  x <- execDriverM state (inferProgram' decls)
  case x of
    Left err -> return (Left err)
    Right (res,x) -> return (Right ((driverEnv x), res))