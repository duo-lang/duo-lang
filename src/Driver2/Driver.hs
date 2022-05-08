module Driver2.Driver
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

import Driver2.Definition
import Driver2.Environment
import Driver2.DepGraph
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
import Syntax.RST.Program qualified as RST
import Syntax.Core.Program as Core
import Syntax.Core.Terms as Core
import TypeAutomata.Simplify
import TypeAutomata.Subsume (subsume)
import TypeInference.Coalescing ( coalesce )
import TypeInference.GenerateConstraints2.Definition
    ( runGenM )
import TypeInference.GenerateConstraints2.Terms
    ( genConstraintsTerm,
      genConstraintsCommand,
      genConstraintsTermRecursive )
import TypeInference.SolveConstraints2 (solveConstraints)
import Utils ( Loc, defaultLoc )
import Syntax.Common.TypesPol
import Sugar.Desugar2 (desugarProgram)

checkAnnot :: PolarityRep pol
           -> TypeScheme pol -- ^ Inferred type
           -> Maybe (TypeScheme pol) -- ^ Annotated type
           -> Loc -- ^ Location for the error message
           -> DriverM (TopAnnot pol)
checkAnnot _ tyInferred Nothing _ = return (Inferred tyInferred)
checkAnnot rep tyInferred (Just tyAnnotated) loc = do
  let isSubsumed = subsume rep tyInferred tyAnnotated
  case isSubsumed of
      (Left err) -> throwError (attachLoc loc err)
      (Right True) -> return (Annotated tyAnnotated)
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
          -> Core.Declaration
          -> DriverM AST.Declaration
--
-- PrdCnsDecl
--
inferDecl mn (Core.PrdCnsDecl loc doc pc isRec fv annot term) = do
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
  let typ = zonk bisubst (AST.getTypeTerm tmInferred)
  guardVerbose $ putStr "\nInferred type: " >> ppPrintIO typ >> putStrLn ""
  -- 5. Simplify
  typSimplified <- if infOptsSimplify infopts then (do
                     printGraphs <- gets (infOptsPrintGraphs . drvOpts)
                     tys <- simplify (generalize typ) printGraphs (T.unpack (unFreeVarName fv))
                     guardVerbose $ putStr "\nInferred type (Simplified): " >> ppPrintIO tys >> putStrLn ""
                     return tys) else return (generalize typ)
  -- 6. Check type annotation.
  ty <- checkAnnot (prdCnsToPol pc) typSimplified annot loc
  -- 7. Insert into environment
  case pc of
    PrdRep -> do
      let f env = env { prdEnv  = M.insert fv (tmInferred ,loc, case ty of Annotated ty -> ty; Inferred ty -> ty) (prdEnv env) }
      modifyEnvironment mn f
      return (AST.PrdCnsDecl loc doc pc isRec fv ty tmInferred)
    CnsRep -> do
      let f env = env { cnsEnv  = M.insert fv (tmInferred, loc, case ty of Annotated ty -> ty; Inferred ty -> ty) (cnsEnv env) }
      modifyEnvironment mn f
      return (AST.PrdCnsDecl loc doc pc isRec fv ty tmInferred)
--
-- CmdDecl
--
inferDecl mn (Core.CmdDecl loc doc v cmd) = do
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
inferDecl mn (Core.DataDecl loc doc dcl) = do
  -- Insert into environment
  let f env = env { declEnv = (loc,dcl) : declEnv env }
  modifyEnvironment mn f
  pure (AST.DataDecl loc doc dcl)
--
-- XtorDecl
--
inferDecl _mn (Core.XtorDecl loc doc dc xt args ret) = do
  pure (AST.XtorDecl loc doc dc xt args ret)
--
-- ImportDecl
--
inferDecl _mn (Core.ImportDecl loc doc mod) = do
  pure (AST.ImportDecl loc doc mod)
--
-- SetDecl
--
inferDecl _mn (Core.SetDecl _ _ txt) = case T.unpack txt of
  _ -> throwOtherError ["Unknown option: " <> txt]
--
-- TyOpDecl
--
inferDecl _mn (Core.TyOpDecl loc doc op prec assoc ty) = do
  pure (AST.TyOpDecl loc doc op prec assoc ty)
--
-- TySynDecl
--
inferDecl _mn (Core.TySynDecl loc doc nm ty) = do
  pure (AST.TySynDecl loc doc nm ty)

inferProgram :: ModuleName -> Core.Program -> DriverM AST.Program
inferProgram mn decls = sequence $ inferDecl mn <$> decls

---------------------------------------------------------------------------------
-- Infer programs
---------------------------------------------------------------------------------

runCompilationModule :: ModuleName -> DriverM ()
runCompilationModule mn = do
  -- Build the dependency graph
  depGraph <- createDepGraph mn
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
      -- 4. Desugar the program
      let desugaredProg = desugarProgram renamedDecls
      -- 5. Infer the declarations
      inferredDecls <- inferProgram mn desugaredProg
      -- 6. Add the renamed AST to the cache
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
        inferProgram mn (desugarProgram renamedDecls)
  res <- execDriverM state action
  case res of
    Left err -> return (Left err)
    Right (res,x) -> return (Right ((drvEnv x), res))

