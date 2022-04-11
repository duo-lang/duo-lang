module Driver.Driver
  ( InferenceOptions(..)
  , defaultInferenceOptions
  , DriverState(..)
  , execDriverM
  , inferProgramIO
  , runCompilationModule
  ) where

import Control.Monad.State
import Control.Monad.Except
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
import Renamer.Definition hiding (getSymbolTables)

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
import Data.List

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
      let newEnv = env { prdEnv  = M.insert fv (tmInferred ,loc, case ty of RST.Annotated ty -> ty; RST.Inferred ty -> ty) (prdEnv env) }
      setEnvironment newEnv
      return (AST.PrdCnsDecl loc doc pc isRec fv ty tmInferred)
    CnsRep -> do
      let newEnv = env { cnsEnv  = M.insert fv (tmInferred, loc, case ty of RST.Annotated ty -> ty; RST.Inferred ty -> ty) (cnsEnv env) }
      setEnvironment newEnv
      return (AST.PrdCnsDecl loc doc pc isRec fv ty tmInferred)
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
  let tn = RST.data_name dcl
  case find (\RST.NominalDecl{..} -> data_name == tn) (snd <$> declEnv env) of
    Just _ ->
        -- HACK: inserting in the environment has already been done in lowering
        -- because the declarations are already needed for lowering
        -- In that case we make sure we don't insert twice
        return (AST.DataDecl loc doc dcl)
    Nothing -> do
      let newEnv = env { declEnv = (loc,dcl) : declEnv env }
      setEnvironment newEnv
      return (AST.DataDecl loc doc dcl)
--
-- XtorDecl
--
inferDecl (RST.XtorDecl loc doc dc xt args ret) = do
  pure (AST.XtorDecl loc doc dc xt args ret)
--
-- ImportDecl
--
inferDecl (RST.ImportDecl loc doc mod) = do
  pure (AST.ImportDecl loc doc mod)
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
--
-- TySynDecl
--
inferDecl (RST.TySynDecl loc doc nm ty) = do
  pure (AST.TySynDecl loc doc nm ty)

inferProgram :: RST.Program -> DriverM AST.Program
inferProgram decls = sequence $ inferDecl <$> decls

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
      liftIO $ putStrLn ("Compiling module: " <> ppPrintString mn)
      -- 1. Find the corresponding file and parse its contents.
      fp <- findModule mn defaultLoc
      file <- liftIO $ T.readFile fp
      decls <- runFileParser fp programP file
      -- 2. Create a symbol table for the module and add it to the Driver state.
      let st :: SymbolTable = createSymbolTable decls
      addSymboltable mn st
      -- 3. Rename the declarations.
      sts <- getSymbolTables
      renamedDecls <- liftEitherErr defaultLoc (runRenamerM sts (renameProgram decls))
      -- 4. Infer the declarations
      inferredDecls <- inferProgram renamedDecls
      -- 5. Add the renamed AST to the cache
      liftIO $ putStrLn ("Compiling module: " <> ppPrintString mn <> " DONE")
      addTypecheckedProgram mn inferredDecls

---------------------------------------------------------------------------------
-- Old
---------------------------------------------------------------------------------


inferProgramIO  :: DriverState -- ^ Initial State
                -> [CST.Declaration]
                -> IO (Either Error (Environment, AST.Program))
inferProgramIO state decls = undefined
  -- x <- execDriverM state (inferProgram decls)
  -- case x of
  --     Left err -> return (Left err)
  --     Right (res,x) -> return (Right ((driverEnv x), res))

