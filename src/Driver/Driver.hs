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
import Text.Megaparsec hiding (Pos)

import Driver.Definition
import Errors
import Parser.Definition ( runFileParser )
import Parser.Program ( programP )
import Pretty.Pretty ( ppPrint, ppPrintIO )
import Syntax.AST.Terms
import Syntax.Common
import Syntax.Lowering.Program
import Syntax.CST.Program qualified as CST
import Syntax.AST.Types
    ( TypeScheme,
      generalize,
      DataDecl(..),
      XtorSig (sig_name, sig_args),
      linearContextToArity
    )
import Syntax.AST.Program
    ( Program,
      Environment(..),
      Declaration(..)
    )
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
import Utils ( Loc )
import Data.List

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
      return (PrdCnsDecl loc pc isRec fv (Just ty) tmInferred)
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
  return (CmdDecl loc v cmdInferred)
--
-- DataDecl
--
inferDecl (DataDecl loc dcl) = do
  -- Insert into environment
  env <- gets driverEnv
  let tn = data_name dcl
  case find (\NominalDecl{..} -> data_name == tn) (snd <$> declEnv env) of
    Just _ ->
        -- HACK: inserting in the environment has already been done in lowering
        -- because the declarations are already needed for lowering
        -- In that case we make sure we don't insert twice
        return (DataDecl loc dcl)
    Nothing -> do
      let ns = case data_refined dcl of
                      Refined -> Refinement
                      NotRefined -> Nominal
      let newEnv = env { declEnv = (loc,dcl) : declEnv env
                       , xtorMap = M.union (M.fromList [((sig_name xt, data_polarity dcl), (ns,linearContextToArity (sig_args xt)))| xt <- fst (data_xtors dcl)]) (xtorMap env)}
      setEnvironment newEnv
      return (DataDecl loc dcl)
--
-- XtorDecl
--
inferDecl (XtorDecl loc dc xt args ret) = do
  env <- gets driverEnv
  let newEnv = env { xtorMap = M.insert (xt,dc) (Structural, fst <$> args) (xtorMap env)}
  setEnvironment newEnv
  pure $ XtorDecl loc dc xt args ret
--
-- ImportDecl
--
inferDecl (ImportDecl loc mod) = do
  fp <- findModule mod loc
  oldEnv <- gets driverEnv
  newEnv <- fst <$> inferProgramFromDisk fp
  setEnvironment (oldEnv <> newEnv)
  return (ImportDecl loc mod)
--
-- SetDecl
--
inferDecl (SetDecl _ txt) = case T.unpack txt of
  _ -> throwOtherError ["Unknown option: " <> txt]

---------------------------------------------------------------------------------
-- Infer programs
---------------------------------------------------------------------------------

inferProgramFromDisk :: FilePath
                     -> DriverM (Environment Inferred, Program Inferred)
inferProgramFromDisk fp = do
  file <- liftIO $ T.readFile fp
  let parsed = runFileParser fp programP file
  case parsed of
    Left err -> throwOtherError [T.pack (errorBundlePretty err)]
    Right decls -> do
      -- Use inference options of parent? Probably not?
      x <- liftIO $ inferProgramIO  (DriverState defaultInferenceOptions { infOptsLibPath = ["examples"] } mempty) decls
      case x of
        Left err -> throwError err
        Right env -> return env

inferProgram :: [CST.Declaration]
             -> DriverM (Program Inferred)
inferProgram decls = do
  decls <- renameProgram decls
  forM decls inferDecl

renameProgram :: [CST.Declaration]
              -> DriverM (Program Parsed)
renameProgram decls = lowerProgram decls

renameProgramIO :: DriverState
                -> [CST.Declaration]
                -> IO (Either Error (Program Parsed))
renameProgramIO state decls = do
  x <- execDriverM state (renameProgram decls)
  case x of
      Left err -> return (Left err)
      Right (res,_) -> return (Right res)

inferProgram' :: Program Parsed
              -> DriverM (Program Inferred)
inferProgram' decls = forM decls inferDecl

inferProgramIO  :: DriverState -- ^ Initial State
                -> [CST.Declaration]
                -> IO (Either Error (Environment Inferred, Program Inferred))
inferProgramIO state decls = do
  x <- execDriverM state (inferProgram decls)
  case x of
      Left err -> return (Left err)
      Right (res,x) -> return (Right ((driverEnv x), res))

inferProgramIO' :: DriverState -- ^ Initial State
                -> Program Parsed
                -> IO (Either Error (Environment Inferred, Program Inferred))
inferProgramIO' state decls = do
  x <- execDriverM state (inferProgram' decls)
  case x of
    Left err -> return (Left err)
    Right (res,x) -> return (Right ((driverEnv x), res))