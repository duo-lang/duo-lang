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
import Resolution.Program (resolveProgram)
import Resolution.SymbolTable
import Resolution.Definition

import Syntax.Common
import Syntax.CST.Program qualified as CST
import Syntax.RST.Program qualified as RST
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Syntax.Core.Program as Core
import TypeAutomata.Simplify
import TypeAutomata.Subsume (subsume)
import TypeInference.Coalescing ( coalesce )
import TypeInference.GenerateConstraints.Definition
    ( runGenM )
import TypeInference.GenerateConstraints.Terms
    ( genConstraintsTerm,
      genConstraintsCommand,
      genConstraintsTermRecursive,
      genConstraintsInstance )
import TypeInference.SolveConstraints (solveConstraints)
import Utils ( Loc, defaultLoc )
import Syntax.Common.TypesPol
import Sugar.Desugar (desugarProgram)

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

inferPrdCnsDeclaration :: ModuleName
                       -> Core.PrdCnsDeclaration pc
                       -> DriverM (TST.PrdCnsDeclaration pc)
inferPrdCnsDeclaration mn Core.MkPrdCnsDeclaration { pcdecl_loc, pcdecl_doc, pcdecl_pc, pcdecl_isRec, pcdecl_name, pcdecl_annot, pcdecl_term} = do
  infopts <- gets drvOpts
  env <- gets drvEnv
  -- 1. Generate the constraints.
  let genFun = case pcdecl_isRec of
        Recursive -> genConstraintsTermRecursive mn pcdecl_loc pcdecl_name pcdecl_pc pcdecl_term
        NonRecursive -> genConstraintsTerm pcdecl_term
  (tmInferred, constraintSet) <- liftEitherErrLoc pcdecl_loc $ runGenM env genFun
  guardVerbose $ ppPrintIO constraintSet
  -- 2. Solve the constraints.
  solverResult <- liftEitherErrLoc pcdecl_loc $ solveConstraints constraintSet env
  guardVerbose $ ppPrintIO solverResult
  -- 3. Coalesce the result
  let bisubst = coalesce solverResult
  guardVerbose $ ppPrintIO bisubst
  -- 4. Read of the type and generate the resulting type
  let typ = zonk bisubst (TST.getTypeTerm tmInferred)
  guardVerbose $ putStr "\nInferred type: " >> ppPrintIO typ >> putStrLn ""
  -- 5. Simplify
  typSimplified <- if infOptsSimplify infopts then (do
                     printGraphs <- gets (infOptsPrintGraphs . drvOpts)
                     tys <- simplify (generalize typ) printGraphs (T.unpack (unFreeVarName pcdecl_name))
                     guardVerbose $ putStr "\nInferred type (Simplified): " >> ppPrintIO tys >> putStrLn ""
                     return tys) else return (generalize typ)
  -- 6. Check type annotation.
  ty <- checkAnnot (prdCnsToPol pcdecl_pc) typSimplified pcdecl_annot pcdecl_loc
  -- 7. Insert into environment
  case pcdecl_pc of
    PrdRep -> do
      let f env = env { prdEnv  = M.insert pcdecl_name (tmInferred ,pcdecl_loc, case ty of Annotated ty -> ty; Inferred ty -> ty) (prdEnv env) }
      modifyEnvironment mn f
      pure TST.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                                   , pcdecl_doc = pcdecl_doc
                                   , pcdecl_pc = pcdecl_pc
                                   , pcdecl_isRec = pcdecl_isRec
                                   , pcdecl_name = pcdecl_name
                                   , pcdecl_annot = ty
                                   , pcdecl_term = tmInferred
                                   }
    CnsRep -> do
      let f env = env { cnsEnv  = M.insert pcdecl_name (tmInferred, pcdecl_loc, case ty of Annotated ty -> ty; Inferred ty -> ty) (cnsEnv env) }
      modifyEnvironment mn f
      pure TST.MkPrdCnsDeclaration { pcdecl_loc = pcdecl_loc
                                   , pcdecl_doc = pcdecl_doc
                                   , pcdecl_pc = pcdecl_pc
                                   , pcdecl_isRec = pcdecl_isRec
                                   , pcdecl_name = pcdecl_name
                                   , pcdecl_annot = ty
                                   , pcdecl_term = tmInferred
                                   }


inferCommandDeclaration :: ModuleName
                        -> Core.CommandDeclaration
                        -> DriverM TST.CommandDeclaration
inferCommandDeclaration mn Core.MkCommandDeclaration { cmddecl_loc, cmddecl_doc, cmddecl_name, cmddecl_cmd } = do
  env <- gets drvEnv
  -- Generate the constraints
  (cmdInferred,constraints) <- liftEitherErrLoc cmddecl_loc $ runGenM env (genConstraintsCommand cmddecl_cmd)
  -- Solve the constraints
  solverResult <- liftEitherErrLoc cmddecl_loc $ solveConstraints constraints env
  guardVerbose $ do
      ppPrintIO constraints
      ppPrintIO solverResult
  -- Insert into environment
  let f env = env { cmdEnv = M.insert cmddecl_name (cmdInferred, cmddecl_loc) (cmdEnv env)}
  modifyEnvironment mn f
  pure TST.MkCommandDeclaration { cmddecl_loc = cmddecl_loc
                                , cmddecl_doc = cmddecl_doc
                                , cmddecl_name = cmddecl_name
                                , cmddecl_cmd = cmdInferred
                                }

inferInstanceDeclaration :: ModuleName
                        -> Core.InstanceDeclaration
                        -> DriverM TST.InstanceDeclaration
inferInstanceDeclaration mn decl@Core.MkInstanceDeclaration { instancedecl_loc, instancedecl_name, instancedecl_typ } = do
  env <- gets drvEnv
  -- Generate the constraints
  (instanceInferred,constraints) <- liftEitherErrLoc instancedecl_loc $ runGenM env (genConstraintsInstance decl)
  -- Solve the constraints
  solverResult <- liftEitherErrLoc instancedecl_loc $ solveConstraints constraints env
  guardVerbose $ do
      ppPrintIO constraints
      ppPrintIO solverResult
  -- Insert into environment
  let f env = env { instanceEnv = M.insert instancedecl_name instancedecl_typ (instanceEnv env)}
  modifyEnvironment mn f
  pure instanceInferred

inferClassDeclaration :: ModuleName 
                      -> RST.ClassDeclaration
                      -> DriverM RST.ClassDeclaration
inferClassDeclaration mn decl@RST.MkClassDeclaration { classdecl_name } = do
  let f env = env { classEnv = M.insert classdecl_name decl (classEnv env)}
  modifyEnvironment mn f
  pure decl


inferDecl :: ModuleName
          -> Core.Declaration
          -> DriverM TST.Declaration
--
-- PrdCnsDecl
--
inferDecl mn (Core.PrdCnsDecl pcrep decl) = do
  decl' <- inferPrdCnsDeclaration mn decl
  pure (TST.PrdCnsDecl pcrep decl')
--
-- CmdDecl
--
inferDecl mn (Core.CmdDecl decl) = do
  decl' <- inferCommandDeclaration mn decl
  pure (TST.CmdDecl decl')
--
-- DataDecl
--
inferDecl mn (Core.DataDecl decl) = do
  -- Insert into environment
  let f env = env { declEnv = (data_loc decl,decl) : declEnv env }
  modifyEnvironment mn f
  pure (TST.DataDecl decl)
--
-- XtorDecl
--
inferDecl _mn (Core.XtorDecl decl) = do
  pure (TST.XtorDecl decl)
--
-- ImportDecl
--
inferDecl _mn (Core.ImportDecl decl) = do
  pure (TST.ImportDecl decl)
--
-- SetDecl
--
inferDecl _mn (Core.SetDecl CST.MkSetDeclaration { setdecl_option }) = 
  throwOtherError ["Unknown option: " <> setdecl_option]
--
-- TyOpDecl
--
inferDecl _mn (Core.TyOpDecl decl) = do
  pure (TST.TyOpDecl decl)
--
-- TySynDecl
--
inferDecl _mn (Core.TySynDecl decl) = do
  pure (TST.TySynDecl decl)
--
-- ClassDecl
--
inferDecl mn (Core.ClassDecl decl) = do
  decl' <- inferClassDeclaration mn decl
  pure (TST.ClassDecl decl')
--
-- InstanceDecl
--
inferDecl mn (Core.InstanceDecl decl) = do
  decl' <- inferInstanceDeclaration mn decl
  pure (TST.InstanceDecl decl')

inferProgram :: ModuleName -> Core.Program -> DriverM TST.Program
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
      -- 3. Resolve the declarations.
      sts <- getSymbolTables
      resolvedDecls <- liftEitherErr (runResolverM sts (resolveProgram decls))
      -- 4. Desugar the program
      let desugaredProg = desugarProgram resolvedDecls
      -- 5. Infer the declarations
      inferredDecls <- inferProgram mn desugaredProg
      -- 6. Add the resolved AST to the cache
      guardVerbose $ putStrLn ("Compiling module: " <> ppPrintString mn <> " DONE")
      addTypecheckedProgram mn inferredDecls

---------------------------------------------------------------------------------
-- Old
---------------------------------------------------------------------------------


inferProgramIO  :: DriverState -- ^ Initial State
                -> ModuleName
                -> [CST.Declaration]
                -> IO (Either Error (Map ModuleName Environment, TST.Program))
inferProgramIO state mn decls = do
  let action :: DriverM TST.Program
      action = do
        st <- createSymbolTable mn decls
        forM_ (imports st) $ \(mn,_) -> runCompilationModule mn
        addSymboltable (MkModuleName "This") st
        sts <- getSymbolTables
        resolvedDecls <- liftEitherErr (runResolverM sts (resolveProgram decls))
        inferProgram mn (desugarProgram resolvedDecls)
  res <- execDriverM state action
  case res of
    Left err -> return (Left err)
    Right (res,x) -> return (Right (drvEnv x, res))

