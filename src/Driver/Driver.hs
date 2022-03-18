module Driver.Driver
  ( InferenceOptions(..)
  , defaultInferenceOptions
  , DriverState(..)
  , execDriverM
  , inferDecl
  -- Rename
  , renameProgram
  , renameProgramFromDecls
  -- Infer
  , inferProgram
  , inferProgramFromDecls
  , inferProgramFromLoweredDecls
  ) where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except
import Data.Map qualified as M
import Data.Text qualified as T
import Data.Text.IO qualified as T

import Driver.Definition
import Errors
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint, ppPrintIO )
import Syntax.AST.Terms
import Syntax.Common
import Syntax.Lowering.Program
import Syntax.AST.Types
    ( TypeScheme,
      generalize,
    )
import Syntax.AST.Program
    ( Program,
      Declaration(..)
    )
import Syntax.CST.Program qualified as CST
import Syntax.Environment (Environment(..))
import Syntax.Zonking (zonkType)
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
import Driver.SymbolTable

checkAnnot :: TypeScheme pol -- ^ Inferred type
           -> Maybe (TypeScheme pol) -- ^ Annotated type
           -> Loc -- ^ Location for the error message
           -> DriverM (TypeScheme pol)
checkAnnot tyInferred Nothing _ = return tyInferred
checkAnnot tyInferred (Just tyAnnotated) loc = do
  let isSubsumed = subsume tyInferred tyAnnotated
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

inferDecl :: Declaration Parsed
           -> DriverM (Declaration Inferred)
--
-- PrdCnsDecl
--
inferDecl (PrdCnsDecl loc pc isRec fv annot term) = do
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
  let typ = zonkType bisubst (getTypeTerm tmInferred)
  guardVerbose $ putStr "\nInferred type: " >> ppPrintIO typ >> putStrLn ""
  -- 5. Simplify
  typSimplified <- case infOptsSimplify infopts of
    True -> do
      printGraphs <- gets (infOptsPrintGraphs . driverOpts)
      tys <- simplify (generalize typ) printGraphs (T.unpack (unFreeVarName fv))
      guardVerbose $ putStr "\nInferred type (Simplified): " >> ppPrintIO tys >> putStrLn ""
      return tys
    False -> return (generalize typ)
  -- 6. Check type annotation.
  ty <- checkAnnot typSimplified annot loc
  -- 7. Insert into environment
  env <- gets driverEnv
  case pc of
    PrdRep -> do
      let newEnv = env { prdEnv  = M.insert fv (tmInferred ,loc, ty) (prdEnv env) }
      setEnvironment newEnv
      return (PrdCnsDecl loc pc isRec fv (Just ty) tmInferred)
    CnsRep -> do
      let newEnv = env { cnsEnv  = M.insert fv (tmInferred, loc, ty) (cnsEnv env) }
      setEnvironment newEnv
      pure (PrdCnsDecl loc pc isRec fv (Just ty) tmInferred)
--
-- CmdDecl
--
inferDecl (CmdDecl loc v cmd) = do
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
  pure (CmdDecl loc v cmdInferred)
--
-- DataDecl
--
inferDecl (DataDecl loc dcl) = do
  env <- gets driverEnv
  let newEnv = env { declEnv = (loc, dcl): declEnv env} 
  setEnvironment newEnv
  pure (DataDecl loc dcl)
--
-- XtorDecl
--
inferDecl (XtorDecl loc dc xt args ret) = do
  pure $ XtorDecl loc dc xt args ret
--
-- ImportDecl
--
inferDecl (ImportDecl loc mod) = do
  pure (ImportDecl loc mod)
--
-- SetDecl
--
inferDecl (SetDecl _ txt) = case T.unpack txt of
  _ -> throwOtherError ["Unknown option: " <> txt]


---------------------------------------------------------------------------------
-- Rename Program
---------------------------------------------------------------------------------

renameProgram :: FilePath
              -> DriverM (Program Parsed, SymbolTable)
renameProgram fp = do
  -- Read and parse file
  file <- liftIO $ T.readFile fp
  decls <- runFileParser fp programP file
  renameProgramFromDecls decls

renameProgramFromDecls :: CST.Program
                       -> DriverM (Program Parsed, SymbolTable)
renameProgramFromDecls decls = do
  -- Compute the symbolTable and dependent modules
  let symbolTable = createSymbolTable decls
  let imports = importedModules symbolTable
  -- Get the symboltables for all imports
  imports <- forM imports $ \imp -> do 
    fp <- findModule imp defaultLoc
    renameProgram fp
  let combinedSymbolTable = mconcat (symbolTable : (snd <$> imports))
  -- Lower program
  lowered <- local (<> combinedSymbolTable) (lowerProgram decls)
  pure (lowered, combinedSymbolTable)

---------------------------------------------------------------------------------
-- Infer programs
---------------------------------------------------------------------------------

inferProgram :: FilePath
             -> DriverM (Program Inferred, SymbolTable, Environment Inferred)
inferProgram fp = do
  -- Read and parse file
  file <- liftIO $ T.readFile fp
  decls <- runFileParser fp programP file
  inferProgramFromDecls decls

inferProgramFromDecls :: CST.Program
                      -> DriverM (Program Inferred, SymbolTable, Environment Inferred)
inferProgramFromDecls decls = do
  -- Compute the symbolTable and dependent modules
  let symbolTable = createSymbolTable decls
  let imports = importedModules symbolTable
  -- Get the symboltables for all imports
  imports <- forM imports $ \imp -> do 
    fp <- findModule imp defaultLoc
    inferProgram fp
  let combinedSymbolTable = mconcat (symbolTable : ((\(_,x,_) -> x) <$> imports))
  let combinedEnv = mconcat ((\(_,_,x) -> x) <$> imports)
  -- Lower program
  lowered <- local (<> combinedSymbolTable) (lowerProgram decls)
  -- Infer program
  setEnvironment combinedEnv
  inferred <- sequence $ inferDecl <$> lowered
  env <- gets driverEnv
  pure (inferred, combinedSymbolTable, env)

inferProgramFromLoweredDecls :: Program Parsed
                             -> DriverM (Program Inferred, Environment Inferred)
inferProgramFromLoweredDecls decls = do
  inferred <- sequence $ inferDecl <$> decls
  env <- gets driverEnv
  pure (inferred, env)
