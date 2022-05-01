module Driver.Driver
  ( InferenceOptions(..)
  , defaultInferenceOptions
  , DriverState(..)
  , execDriverM
  , inferProgramIO
  , inferDecl
  , runCompilationModule
  ) where

import Control.Monad.State
import Control.Monad.Except
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Text.IO qualified as T

import Driver.Definition
import Driver.Environment 
import Driver.DepGraph
import Errors
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint, ppPrintIO, ppPrintString )
import Renamer.Program (renameProgram)
import Renamer.SymbolTable
import Renamer.Definition

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
import Utils ( Loc, defaultLoc )

checkAnnot :: PolarityRep pol
           -> RST.TypeScheme pol -- ^ Inferred type
           -> Maybe (RST.TypeScheme pol) -- ^ Annotated type
           -> Loc -- ^ Location for the error message
           -> DriverM (RST.TopAnnot pol)
checkAnnot _ tyInferred Nothing _ = return (RST.Inferred tyInferred)
checkAnnot rep tyInferred (Just tyAnnotated) loc = do
  let isSubsumed = subsume rep tyInferred tyAnnotated
  case isSubsumed of
      (Left err) -> throwError (attachLoc loc err)
      (Right True) -> return (RST.Annotated tyAnnotated)
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

inferDecl :: ModuleName
          -> RST.Declaration
          -> DriverM AST.Declaration
--
-- PrdCnsDecl
--
inferDecl mn (RST.PrdCnsDecl loc doc pc isRec fv annot term) = do
  infopts <- gets drvOpts
  env <- gets drvEnv
  -- 1. Generate the constraints.
  let genFun = case isRec of
        Recursive -> genConstraintsTermRecursive mn loc fv pc term
        NonRecursive -> genConstraintsTerm term
  (tmInferred, constraintSet) <- liftEitherErrLoc loc $ runGenM env genFun
  guardVerbose $ ppPrintIO constraintSet
  -- 2. Solve the constraints.
  solverResult <- liftEitherErrLoc loc $ solveConstraints constraintSet env
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
      printGraphs <- gets (infOptsPrintGraphs . drvOpts)
      tys <- simplify (RST.generalize typ) printGraphs (T.unpack (unFreeVarName fv))
      guardVerbose $ putStr "\nInferred type (Simplified): " >> ppPrintIO tys >> putStrLn ""
      return tys
    False -> return (RST.generalize typ)
  -- 6. Check type annotation.
  ty <- checkAnnot (prdCnsToPol pc) typSimplified annot loc
  -- 7. Insert into environment
  case pc of
    PrdRep -> do
      let f env = env { prdEnv  = M.insert fv (tmInferred ,loc, case ty of RST.Annotated ty -> ty; RST.Inferred ty -> ty) (prdEnv env) }
      modifyEnvironment mn f
      return (AST.PrdCnsDecl loc doc pc isRec fv ty tmInferred)
    CnsRep -> do
      let f env = env { cnsEnv  = M.insert fv (tmInferred, loc, case ty of RST.Annotated ty -> ty; RST.Inferred ty -> ty) (cnsEnv env) }
      modifyEnvironment mn f
      return (AST.PrdCnsDecl loc doc pc isRec fv ty tmInferred)
--
-- CmdDecl
--
inferDecl mn (RST.CmdDecl loc doc v cmd) = do
  env <- gets drvEnv
  -- Generate the constraints
  (cmdInferred,constraints) <- liftEitherErrLoc loc $ runGenM env (genConstraintsCommand cmd)
  -- Solve the constraints
  solverResult <- liftEitherErrLoc loc $ solveConstraints constraints env
  guardVerbose $ do
      ppPrintIO constraints
      ppPrintIO solverResult
  -- Insert into environment
  let f env = env { cmdEnv  = M.insert v (cmdInferred, loc) (cmdEnv env)}
  modifyEnvironment mn f
  return (AST.CmdDecl loc doc v cmdInferred)
--
-- DataDecl
--
inferDecl mn (RST.DataDecl loc doc dcl) = do
  -- Insert into environment
  let f env = env { declEnv = (loc,dcl) : declEnv env }
  modifyEnvironment mn f
  pure (AST.DataDecl loc doc dcl)
--
-- XtorDecl
--
inferDecl _mn (RST.XtorDecl loc doc dc xt args ret) = do
  pure (AST.XtorDecl loc doc dc xt args ret)
--
-- ImportDecl
--
inferDecl _mn (RST.ImportDecl loc doc mod) = do
  pure (AST.ImportDecl loc doc mod)
--
-- SetDecl
--
inferDecl _mn (RST.SetDecl _ _ txt) = case T.unpack txt of
  _ -> throwOtherError ["Unknown option: " <> txt]
--
-- TyOpDecl
--
inferDecl _mn (RST.TyOpDecl loc doc op prec assoc ty) = do
  pure (AST.TyOpDecl loc doc op prec assoc ty)
--
-- TySynDecl
--
inferDecl _mn (RST.TySynDecl loc doc nm ty) = do
  pure (AST.TySynDecl loc doc nm ty)

inferProgram :: ModuleName -> RST.Program -> DriverM AST.Program
inferProgram mn decls = sequence $ inferDecl mn <$> decls

---------------------------------------------------------------------------------
-- Infer programs
---------------------------------------------------------------------------------
  
runCompilationModule :: ModuleName -> DriverM ()
runCompilationModule mn = do
  -- Build the dependency graph
  depGraph <- createDepGraph [mn]
  -- Create the compilation order
  compilationOrder <- topologicalSort depGraph
  runCompilationPlan compilationOrder
  
runCompilationPlan :: CompilationOrder -> DriverM ()
runCompilationPlan compilationOrder = forM_ compilationOrder compileModule
  where
    compileModule :: ModuleName -> DriverM ()
    compileModule mn = do
      guardVerbose $ putStrLn ("Compiling module: " <> ppPrintString mn)
      -- 1. Find the corresponding file and parse its contents.
      fp <- findModule mn defaultLoc
      file <- liftIO $ T.readFile fp
      decls <- runFileParser fp programP file
      -- 2. Create a symbol table for the module and add it to the Driver state.
      st <- createSymbolTable mn decls
      addSymboltable mn st
      -- 3. Rename the declarations.
      sts <- getSymbolTables
      renamedDecls <- liftEitherErr (runRenamerM sts (renameProgram decls))
      -- 4. Infer the declarations
      inferredDecls <- inferProgram mn renamedDecls
      -- 5. Add the renamed AST to the cache
      guardVerbose $ putStrLn ("Compiling module: " <> ppPrintString mn <> " DONE")
      addTypecheckedProgram mn inferredDecls

---------------------------------------------------------------------------------
-- Old
---------------------------------------------------------------------------------


inferProgramIO  :: DriverState -- ^ Initial State
                -> ModuleName
                -> [CST.Declaration]
                -> IO (Either Error (Map ModuleName Environment, AST.Program))
inferProgramIO state mn decls = do
  let action :: DriverM (AST.Program)
      action = do
        st <- createSymbolTable mn decls
        forM_ (imports st) $ \(mn,_) -> runCompilationModule mn
        addSymboltable (MkModuleName "This") st
        sts <- getSymbolTables
        renamedDecls <- liftEitherErr (runRenamerM sts (renameProgram decls))
        inferProgram mn renamedDecls
  res <- execDriverM state action
  case res of
    Left err -> return (Left err)
    Right (res,x) -> return (Right ((drvEnv x), res))

