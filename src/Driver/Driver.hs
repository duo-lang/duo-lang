module Driver.Driver
  ( InferenceOptions(..)
  , defaultInferenceOptions
  , DriverState(..)
  , execDriverM
  , inferProgramIO
  , inferDecl
  , runCompilationModule
  , adjustModulePath
  ) where

import Control.Monad.State
import Control.Monad.Except
import Data.List.NonEmpty ( NonEmpty ((:|)) )
import Data.List.NonEmpty qualified as NE
import System.FilePath (joinPath, splitDirectories, dropExtension)
import Data.List ( isPrefixOf, stripPrefix )
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T
import Driver.Definition
import TypeInference.Environment
import Driver.DepGraph
import Errors
import Errors.Renamer
import Pretty.Pretty ( ppPrint, ppPrintIO, ppPrintString )
import Resolution.Program (resolveModule)
import Resolution.Definition

import Syntax.CST.Names
import Syntax.RST.Kinds
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types ( PrdCnsRep(..), PolyKind(..))
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
import TypeInference.SolveConstraints (solveConstraints, solveClassConstraints)
import Loc ( Loc, AttachLoc(attachLoc), defaultLoc, getLoc)
import Syntax.RST.Types (PolarityRep(..))
import Syntax.TST.Types qualified as TST
import Syntax.RST.Program (prdCnsToPol)
import Sugar.Desugar (Desugar(..))
import qualified Data.Set as S
import Data.Maybe (catMaybes)
import Pretty.Common (Header(..))
import Pretty.Program ()
import Translate.InsertInstance (InsertInstance(insertInstance))
import Syntax.RST.Types qualified as RST
import TypeAutomata.Intersection (intersectIsEmpty)
import Data.Bifunctor (Bifunctor(first))

checkPolyKind :: Loc -> TST.Typ pol -> DriverM ()
checkPolyKind loc ty = case TST.getKind ty of
  MkPknd (MkPolyKind (_:_) _) -> throwOtherError loc ["Type " <> ppPrint ty <> " was not fully applied"]
  _ -> return ()

getAnnotKind :: TST.Typ pol -> Maybe (TST.TypeScheme pol) -> Maybe (KVar, AnyKind)
getAnnotKind tyInf maybeAnnot =
  case (TST.getKind tyInf,maybeAnnot) of
    (MkPknd (KindVar kv),Just annot) -> Just (kv,TST.getKind annot.ts_monotype)
    _ -> Nothing

checkKindAnnot :: Loc -> RST.TypeScheme pol -> DriverM (TST.TypeScheme pol)
checkKindAnnot loc tyAnnotated = do
  env <- gets (\x -> x.drvEnv)
  (annotChecked, annotConstrs) <- liftEitherErr $ runGenM loc env (annotateKind tyAnnotated)
  solverResAnnot <- liftEitherErrLoc loc $ solveConstraints annotConstrs Nothing env
  let bisubstAnnot = coalesce solverResAnnot
  let typAnnotZonked = TST.zonk TST.UniRep bisubstAnnot annotChecked
  checkPolyKind loc typAnnotZonked.ts_monotype
  return typAnnotZonked

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
inferPrdCnsDeclaration mn decl = do
  infopts <- gets (\x -> x.drvOpts)
  env <- gets (\x -> x.drvEnv)
  -- 1. Generate the constraints.
  let genFun = case decl.pcdecl_isRec of
        CST.Recursive -> genConstraintsTermRecursive mn decl.pcdecl_loc decl.pcdecl_name decl.pcdecl_pc decl.pcdecl_term
        CST.NonRecursive -> genConstraints decl.pcdecl_term
  (tmInferred, constraintSet) <- liftEitherErr (runGenM decl.pcdecl_loc env genFun)
  guardVerbose $ do
    ppPrintIO (Header decl.pcdecl_name.unFreeVarName)
    ppPrintIO ("" :: T.Text)
    ppPrintIO decl.pcdecl_term
    ppPrintIO ("" :: T.Text)
    ppPrintIO constraintSet
  -- 2. Solve the constraints.
  tyAnnotChecked <- mapM (checkKindAnnot decl.pcdecl_loc) (decl.pcdecl_annot)
  let tyInf = TST.getTypeTerm tmInferred
  let annotKind = getAnnotKind tyInf tyAnnotChecked
  solverResult <- liftEitherErrLoc decl.pcdecl_loc $ solveConstraints constraintSet annotKind env
  guardVerbose $ ppPrintIO solverResult
  -- 3. Coalesce the result
  let bisubst = coalesce solverResult
  guardVerbose $ ppPrintIO bisubst
  -- 4. Solve the type class constraints.
  instances <- liftEitherErrLoc decl.pcdecl_loc $ solveClassConstraints solverResult bisubst env
  guardVerbose $ ppPrintIO instances
  tmInferred <- liftEitherErrLoc decl.pcdecl_loc (insertInstance instances tmInferred)
  -- 5. Read of the type and generate the resulting type
  let typ = TST.zonk TST.UniRep bisubst (TST.getTypeTerm tmInferred)
  checkPolyKind (getLoc typ) typ
  guardVerbose $ putStr "\nInferred type: " >> ppPrintIO typ >> putStrLn ""
  -- 6. Simplify
  typSimplified <- if infopts.infOptsSimplify then (do
                     printGraphs <- gets (\x -> x.drvOpts.infOptsPrintGraphs)
                     tys <- simplify (TST.generalize typ) printGraphs (T.unpack decl.pcdecl_name.unFreeVarName)
                     guardVerbose $ putStr "\nInferred type (Simplified): " >> ppPrintIO tys >> putStrLn ""
                     return tys) else return (TST.generalize typ)
  -- 6. Check type annotation.
  ty <- checkAnnot (prdCnsToPol decl.pcdecl_pc) typSimplified tyAnnotChecked decl.pcdecl_loc
  -- 7. Insert into environment
  case decl.pcdecl_pc of
    PrdRep -> do
      let f env = env { prdEnv  = M.insert decl.pcdecl_name (tmInferred ,decl.pcdecl_loc, case ty of TST.Annotated ty -> ty; TST.Inferred ty -> ty) env.prdEnv }
      modifyEnvironment mn f
      pure TST.MkPrdCnsDeclaration { pcdecl_loc = decl.pcdecl_loc
                                   , pcdecl_doc = decl.pcdecl_doc
                                   , pcdecl_pc = decl.pcdecl_pc
                                   , pcdecl_isRec = decl.pcdecl_isRec
                                   , pcdecl_name = decl.pcdecl_name
                                   , pcdecl_annot = ty
                                   , pcdecl_term = tmInferred
                                   }
    CnsRep -> do
      let f env = env { cnsEnv  = M.insert decl.pcdecl_name (tmInferred, decl.pcdecl_loc, case ty of TST.Annotated ty -> ty; TST.Inferred ty -> ty) env.cnsEnv }
      modifyEnvironment mn f
      pure TST.MkPrdCnsDeclaration { pcdecl_loc = decl.pcdecl_loc
                                   , pcdecl_doc = decl.pcdecl_doc
                                   , pcdecl_pc = decl.pcdecl_pc
                                   , pcdecl_isRec = decl.pcdecl_isRec
                                   , pcdecl_name = decl.pcdecl_name
                                   , pcdecl_annot = ty
                                   , pcdecl_term = tmInferred
                                   }


inferCommandDeclaration :: ModuleName
                        -> Core.CommandDeclaration
                        -> DriverM TST.CommandDeclaration
inferCommandDeclaration mn decl = do
  env <- gets (\x -> x.drvEnv)
  -- Generate the constraints
  (cmdInferred,constraints) <- liftEitherErr (runGenM decl.cmddecl_loc env (genConstraints decl.cmddecl_cmd))
  -- Solve the constraints
  solverResult <- liftEitherErrLoc decl.cmddecl_loc $ solveConstraints constraints Nothing env
  guardVerbose $ do
    ppPrintIO (Header decl.cmddecl_name.unFreeVarName)
    ppPrintIO ("" :: T.Text)
    ppPrintIO decl.cmddecl_cmd
    ppPrintIO ("" :: T.Text)
    ppPrintIO constraints
    ppPrintIO solverResult
  -- Coalesce the result
  let bisubst = coalesce solverResult
  guardVerbose $ ppPrintIO bisubst
  -- Solve the type class constraints.
  instances <- liftEitherErrLoc decl.cmddecl_loc $ solveClassConstraints solverResult bisubst env
  guardVerbose $ ppPrintIO instances
  cmdInferred <- liftEitherErrLoc decl.cmddecl_loc (insertInstance instances cmdInferred)
  -- Insert into environment
  let f env = env { cmdEnv = M.insert decl.cmddecl_name (cmdInferred, decl.cmddecl_loc) env.cmdEnv }
  modifyEnvironment mn f
  pure TST.MkCommandDeclaration { cmddecl_loc = decl.cmddecl_loc
                                , cmddecl_doc = decl.cmddecl_doc
                                , cmddecl_name = decl.cmddecl_name
                                , cmddecl_cmd = cmdInferred
                                }

inferInstanceDeclaration :: ModuleName
                        -> Core.InstanceDeclaration
                        -> DriverM TST.InstanceDeclaration
inferInstanceDeclaration mn decl= do
  env <- gets (\x -> x.drvEnv)
  -- Generate the constraints
  (instanceInferred,constraints) <- liftEitherErr (runGenM decl.instancedecl_loc env (genConstraints decl))
  -- Solve the constraints
  solverResult <- liftEitherErrLoc decl.instancedecl_loc $ solveConstraints constraints Nothing env
  guardVerbose $ do
    ppPrintIO (Header  $ decl.instancedecl_class.unClassName <> " " <> ppPrint (fst decl.instancedecl_typ))
    ppPrintIO ("" :: T.Text)
    ppPrintIO (Core.InstanceDecl decl)
    ppPrintIO ("" :: T.Text)
    ppPrintIO constraints
    ppPrintIO solverResult
  -- Insert instance into environment to allow recursive method definitions
  let (typ, tyn) = instanceInferred.instancedecl_typ
  checkOverlappingInstances decl.instancedecl_loc decl.instancedecl_class (typ, tyn)
  let iname = instanceInferred.instancedecl_name
  let f env = env { instanceEnv = M.adjust (S.insert (iname, typ, tyn)) decl.instancedecl_class env.instanceEnv }
  modifyEnvironment mn f
  -- Coalesce the result
  let bisubst = coalesce solverResult
  guardVerbose $ ppPrintIO bisubst
  -- Solve the type class constraints.
  env <- gets (\x -> x.drvEnv)
  instances <- liftEitherErrLoc decl.instancedecl_loc $ solveClassConstraints solverResult bisubst env
  guardVerbose $ ppPrintIO instances
  instanceInferred <- liftEitherErrLoc decl.instancedecl_loc (insertInstance instances instanceInferred)
  -- Insert inferred instance into environment   
  let f env = env { instanceDeclEnv = M.insert decl.instancedecl_name instanceInferred env.instanceDeclEnv}
  modifyEnvironment mn f
  pure instanceInferred

-- | For each instance of the same class in the environment, check whether it is a sub- or supertype of the declared instance type.
checkOverlappingInstances :: Loc -> ClassName -> (TST.Typ RST.Pos, TST.Typ RST.Neg) -> DriverM ()
checkOverlappingInstances loc cn (typ, tyn) = do
  env <- gets (\x -> x.drvEnv)
  let instances = M.unions . fmap (\x -> x.instanceEnv) . M.elems $ env
  case M.lookup cn instances of
    Nothing -> pure () -- No overlapping instances
    Just insts -> mapM_ (checkOverlap loc (typ, tyn)) (S.toList insts)
  where checkOverlap :: Loc -> (TST.Typ RST.Pos, TST.Typ RST.Neg) -> (FreeVarName, TST.Typ RST.Pos, TST.Typ RST.Neg) -> DriverM ()
        checkOverlap loc (typ, tyn) (inst, typ', tyn') = do
          printGraphs <- gets (\x -> x.drvOpts.infOptsPrintGraphs)
          let err = ErrOther $ SomeOtherError loc $ T.unlines [ "The instance declared is overlapping and violates type class coherence."
                                                              , " Conflicting instance " <> ppPrint inst <> " : " <> ppPrint cn <> " " <> ppPrint typ'
                                                              ]
          emptyIntersectionPos <- intersectIsEmpty printGraphs (TST.generalize typ) (TST.generalize typ')
          emptyIntersectionNeg <- intersectIsEmpty printGraphs (TST.generalize tyn) (TST.generalize tyn')
          unless (emptyIntersectionPos && emptyIntersectionNeg) (throwError (err NE.:| []))

inferClassDeclaration :: ModuleName
                      -> RST.ClassDeclaration
                      -> DriverM RST.ClassDeclaration
inferClassDeclaration mn decl = do
  let f env = env { classEnv = M.insert decl.classdecl_name decl env.classEnv
                  , instanceEnv = M.insert decl.classdecl_name S.empty env.instanceEnv }
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
  let loc = decl.data_loc
  env <- gets (\x->x.drvEnv)
  decl' <- liftEitherErrLoc loc (resolveDataDecl decl env)
  let f env = env { declEnv = (loc, decl') : env.declEnv}
  modifyEnvironment mn f
  pure (TST.DataDecl decl')

--
-- XtorDecl
--
inferDecl _mn (Core.XtorDecl decl) = do
  -- check constructor kinds
  let xtornm = decl.strxtordecl_name
  let f env = env { xtorEnv = M.insert xtornm decl env.xtorEnv}
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
inferDecl _mn (Core.SetDecl decl) =
  throwOtherError decl.loc ["Unknown option: " <> decl.option]
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
inferProgram mod = do
  let inferDecl' :: Core.Declaration -> DriverM (Maybe TST.Declaration)
      inferDecl' d = catchError (Just <$> inferDecl mod.mod_name d) (addErrorsNonEmpty mod.mod_name Nothing)
  newDecls <- catMaybes <$> mapM inferDecl' mod.mod_decls
  pure TST.MkModule { mod_name = mod.mod_name
                    , mod_libpath = mod.mod_libpath
                    , mod_decls = newDecls
                    }


-- when only given a filepath, parsing the file will result in the libpath of a module overlapping with the module name, e.g.
-- module Codata.Function in std/Codata/Function.duo will have libpath `std/Codata`.
-- Thus we have to adjust the libpath (to `std/` in the example above).
-- Moreover, we need to check whether the new path and the original filepath are compatible.
adjustModulePath :: CST.Module -> FilePath -> Either (NE.NonEmpty Error) CST.Module
adjustModulePath mod fp =
  let fp'  = fpToList fp
      mlp  = mod.libpath
      mFp  = fpToList mlp
      mn   = mod.name
      mp   = T.unpack <$> mn.mn_path ++ [mn.mn_base]
  in do
    prefix <- reverse <$> dropModulePart (reverse mp) (reverse mFp)
    if prefix `isPrefixOf` fp'
    then pure mod { CST.libpath = joinPath prefix }
    else throwOtherError defaultLoc [ "Module name " <> T.pack (ppPrintString mlp) <> " is not compatible with given filepath " <> T.pack fp ]
  where
    fpToList :: FilePath -> [String]
    fpToList = splitDirectories . dropExtension

    dropModulePart :: [String] -> [String] -> Either (NE.NonEmpty Error) [String]
    dropModulePart mp mFp =
      case stripPrefix mp mFp of
        Just mFp' -> pure mFp'
        Nothing   -> throwOtherError defaultLoc [ "Module name " <> T.pack (ppPrintString mod.name) <> " is not a suffix of path " <> T.pack mod.libpath]


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
      let helper :: (a -> a') -> (Either a b, c) -> (Either a' b, c)
          helper f (x,y) = (first f x, y)
      resolvedDecls <- liftEitherErr (helper (\err -> ErrResolution err :| []) (runResolverM (ResolveReader sts mempty mempty) (resolveModule decls)))
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
inferProgramIO state mod = do
  let action :: DriverM TST.Module
      action = do
        addModule mod
        runCompilationModule mod.name
        queryTypecheckedModule mod.name
  res <- execDriverM state action
  case res of
    (Left err, warnings) -> return (Left err, warnings)
    (Right (res,x), warnings) -> return (Right (x.drvEnv, res), warnings)

