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
import Data.List.NonEmpty ( NonEmpty ((:|)) )
import Data.List.NonEmpty qualified as NE
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T
import Driver.Definition
import Driver.Environment
import Driver.DepGraph
import Errors
import Pretty.Pretty ( ppPrint, ppPrintIO, ppPrintString )
import Resolution.Program (resolveModule)
import Resolution.Definition

import Syntax.CST.Names
import Syntax.CST.Kinds (MonoKind(CBox))
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types ( PrdCnsRep(..))
import Syntax.RST.Program qualified as RST
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Syntax.Core.Program as Core
import TypeAutomata.Simplify
import TypeAutomata.Subsume (subsume)
import TypeInference.Coalescing ( coalesce )
import TypeInference.GenerateConstraints.Definition
    ( runGenM )
import TypeInference.GenerateConstraints.Kinds
import TypeInference.GenerateConstraints.Terms
    ( GenConstraints(..),
      genConstraintsTermRecursive )
import TypeInference.SolveConstraints (solveConstraints)
import Loc ( Loc, AttachLoc(attachLoc) )
import Syntax.RST.Types (PolarityRep(..))
import Syntax.TST.Types qualified as TST
import Syntax.RST.Program (prdCnsToPol)
import Sugar.Desugar (Desugar(..))
import qualified Data.Set as S
import Data.Maybe (catMaybes)
import Pretty.Common (Header(..))
import Pretty.Program ()


checkAnnot :: PolarityRep pol
           -> TST.TypeScheme pol -- ^ Inferred type
           -> Maybe (TST.TypeScheme pol) -- ^ Annotated type
           -> Loc -- ^ Location for the error message
           -> DriverM (TST.TopAnnot pol)
checkAnnot _ tyInferred Nothing _ = return (TST.Inferred tyInferred)
checkAnnot rep tyInferred (Just tyAnnotated) loc = do
  let isSubsumed = subsume rep tyInferred tyAnnotated
  case isSubsumed of
      (Left err) -> throwError (attachLoc loc <$> err)
      (Right True) -> return (TST.Annotated tyAnnotated)
      (Right False) -> do

        let err = ErrOther $ SomeOtherError loc $ T.unlines [ "Annotated type is not subsumed by inferred type"
                                                            , " Annotated type: " <> ppPrint tyAnnotated
                                                            , " Inferred type:  " <> ppPrint tyInferred
                                                            ]
        guardVerbose $ ppPrintIO err
        throwError (err NE.:| [])

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
        CST.Recursive -> genConstraintsTermRecursive mn pcdecl_loc pcdecl_name pcdecl_pc pcdecl_term
        CST.NonRecursive -> genConstraints pcdecl_term
  (tmInferred, constraintSet) <- liftEitherErr (runGenM pcdecl_loc env genFun)
  guardVerbose $ do
    ppPrintIO (Header (unFreeVarName pcdecl_name))
    ppPrintIO ("" :: T.Text)
    ppPrintIO pcdecl_term
    ppPrintIO ("" :: T.Text)
    ppPrintIO constraintSet
  -- 2. Solve the constraints.
  solverResult <- liftEitherErrLoc pcdecl_loc $ solveConstraints constraintSet env
  guardVerbose $ ppPrintIO solverResult
  -- 3. Coalesce the result
  let bisubst = coalesce solverResult
  guardVerbose $ ppPrintIO bisubst
  -- 4. Read of the type and generate the resulting type
  let typ = TST.zonk TST.UniRep bisubst (TST.getTypeTerm tmInferred)
  guardVerbose $ putStr "\nInferred type: " >> ppPrintIO typ >> putStrLn ""
  -- 5. Simplify
  typSimplified <- if infOptsSimplify infopts then (do
                     printGraphs <- gets (infOptsPrintGraphs . drvOpts)
                     tys <- simplify (TST.generalize typ) printGraphs (T.unpack (unFreeVarName pcdecl_name))
                     guardVerbose $ putStr "\nInferred type (Simplified): " >> ppPrintIO tys >> putStrLn ""
                     return tys) else return (TST.generalize typ)
  -- 6. Check type annotation.
  --  annot <- liftEitherErrLoc pcdecl_loc (fst $ runGenM pcdecl_loc env (annotateMaybeTypeScheme pcdecl_annot) )
  annot <- maybe (return Nothing) (Just . fst <$>) $ liftEitherErrLoc pcdecl_loc . fst . runGenM pcdecl_loc env . annotateKind <$> pcdecl_annot
  ty <- checkAnnot (prdCnsToPol pcdecl_pc) typSimplified annot pcdecl_loc
  -- 7. Insert into environment
  case pcdecl_pc of
    PrdRep -> do
      let f env = env { prdEnv  = M.insert pcdecl_name (tmInferred ,pcdecl_loc, case ty of TST.Annotated ty -> ty; TST.Inferred ty -> ty) (prdEnv env) }
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
      let f env = env { cnsEnv  = M.insert pcdecl_name (tmInferred, pcdecl_loc, case ty of TST.Annotated ty -> ty; TST.Inferred ty -> ty) (cnsEnv env) }
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
  (cmdInferred,constraints) <- liftEitherErr (runGenM cmddecl_loc env (genConstraints cmddecl_cmd))
  -- Solve the constraints
  solverResult <- liftEitherErrLoc cmddecl_loc $ solveConstraints constraints env
  guardVerbose $ do
    ppPrintIO (Header (unFreeVarName cmddecl_name))
    ppPrintIO ("" :: T.Text)
    ppPrintIO cmddecl_cmd
    ppPrintIO ("" :: T.Text)
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
  (instanceInferred,constraints) <- liftEitherErr (runGenM instancedecl_loc env (genConstraints decl))
  -- Solve the constraints
  solverResult <- liftEitherErrLoc instancedecl_loc $ solveConstraints constraints env
  guardVerbose $ do
    ppPrintIO (Header  $ unClassName instancedecl_name <> " " <> ppPrint (fst instancedecl_typ))
    ppPrintIO ("" :: T.Text)
    ppPrintIO (Core.InstanceDecl decl)
    ppPrintIO ("" :: T.Text)
    ppPrintIO constraints
    ppPrintIO solverResult
  -- Insert into environment
  let instty' = TST.instancedecl_typ instanceInferred
  let f env = env { instanceEnv = M.adjust (S.insert instty') instancedecl_name (instanceEnv env)}
  modifyEnvironment mn f
  pure instanceInferred

inferClassDeclaration :: ModuleName
                      -> RST.ClassDeclaration
                      -> DriverM RST.ClassDeclaration
inferClassDeclaration mn decl@RST.MkClassDeclaration { classdecl_name } = do
  let f env = env { classEnv = M.insert classdecl_name decl (classEnv env)
                  , instanceEnv = M.insert classdecl_name S.empty (instanceEnv env) }
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
  let loc = RST.data_loc decl
  env <- gets drvEnv
  decl' <- liftEitherErrLoc loc (resolveDataDecl decl env)
  let f env = env { declEnv = (loc, decl') : declEnv env} 
  modifyEnvironment mn f
  pure (TST.DataDecl decl')
 
--
-- XtorDecl
--
inferDecl _mn (Core.XtorDecl decl) = do
  -- check constructor kinds
  let retKnd = CBox $ RST.strxtordecl_evalOrder decl
  let xtornm = RST.strxtordecl_name decl
  let argKnds = map snd (RST.strxtordecl_arity decl)
  let f env = env { kindEnv = M.insert xtornm (retKnd, argKnds) (kindEnv env)}
  modifyEnvironment _mn f
  pure (TST.XtorDecl decl)
--
-- ImportDecl
--
inferDecl _mn (Core.ImportDecl decl) = do

  pure (TST.ImportDecl decl)
--
-- SetDecl
--
inferDecl _mn (Core.SetDecl CST.MkSetDeclaration { setdecl_option, setdecl_loc }) =
  throwOtherError setdecl_loc ["Unknown option: " <> setdecl_option]
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

inferProgram :: Core.Module -> DriverM TST.Module
inferProgram Core.MkModule { mod_name, mod_fp, mod_decls } = do
  let inferDecl' :: Core.Declaration -> DriverM (Maybe TST.Declaration)
      inferDecl' d = catchError (Just <$> inferDecl mod_name d) (addErrorsNonEmpty mod_name Nothing)
  newDecls <- catMaybes <$> mapM inferDecl' mod_decls
  pure TST.MkModule { mod_name = mod_name
                    , mod_fp = mod_fp
                    , mod_decls = newDecls
                    }


    

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
runCompilationPlan compilationOrder = do
  forM_ compilationOrder compileModule
  --  errs <- concat <$> mapM (gets . flip getModuleErrorsTrans) compilationOrder
  errs <- case reverse compilationOrder of
            [] -> return []
            (m:_) -> gets $ flip getModuleErrorsTrans m
  case errs of
    [] -> return ()
    (e:es) -> throwError (e :| es)
  where
    compileModule :: ModuleName -> DriverM ()
    compileModule mn = do
      guardVerbose $ putStrLn ("Compiling module: " <> ppPrintString mn)
      -- 1. Find the corresponding file and parse its contents.
      --  decls <- getModuleDeclarations mn
      decls <- getModuleDeclarations mn
      -- 2. Create a symbol table for the module and add it to the Driver state.
      st <- getSymbolTable decls
      addSymboltable mn st
      -- 3. Resolve the declarations.
      sts <- getSymbolTables
      resolvedDecls <- liftEitherErr (runResolverM (ResolveReader sts mempty) (resolveModule decls))
      -- 4. Desugar the program
      let desugaredProg = desugar resolvedDecls
      -- 5. Infer the declarations
      inferredDecls <- inferProgram desugaredProg
      -- 6. Add the resolved AST to the cache
      guardVerbose $ putStrLn ("Compiling module: " <> ppPrintString mn <> " DONE")
      addTypecheckedModule mn inferredDecls

---------------------------------------------------------------------------------
-- Old
---------------------------------------------------------------------------------

inferProgramIO  :: DriverState -- ^ Initial State
                -> CST.Module
                -> IO (Either (NonEmpty Error) (Map ModuleName Environment, TST.Module),[Warning])
inferProgramIO state decls = do
  let action :: DriverM TST.Module
      action = do
        addModule decls
        runCompilationModule (CST.mod_name decls)
        queryTypecheckedModule (CST.mod_name decls)
  res <- execDriverM state action
  case res of
    (Left err, warnings) -> return (Left err, warnings)
    (Right (res,x), warnings) -> return (Right (drvEnv x, res), warnings)

