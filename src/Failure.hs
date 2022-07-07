module Failure where
import qualified Data.Text.IO as T
import Control.Monad.Except (runExcept)
import Parser.Definition (runFileParser)
import Parser.Program (programP)
import Driver.Driver (inferProgramIO, execDriverM, inferDecl)
import Driver.Definition (defaultDriverState, DriverM (DriverM), addSymboltable, getSymbolTables, liftEitherErr, DriverState (drvEnv))
import Syntax.Common (ModuleName(MkModuleName))
import Resolution.SymbolTable (createSymbolTable)
import Resolution.Definition (runResolverM)
import Resolution.Program (resolveProgram)
import Data.Either (isRight, isLeft)
import Control.Monad (guard)
import Sugar.Desugar (desugarProgram)
import qualified Syntax.Core.Program as Core
import qualified Syntax.TST.Program as TST
import qualified Syntax.RST.Program as RST
import qualified Syntax.CST.Program as CST

failureProg = do
  Right fun <- (\fp -> T.readFile fp  >>= return . runExcept . runFileParser fp programP) "examples/Function.ds"

  -- works
  -- codata Fun ...
  -- type operator -> ...
  works <- inferProgramIO defaultDriverState (MkModuleName "works") $ take 2 fun
  guard (isRight works)
  -- fails
  -- ...
  -- id : forall a . a -> a := \x => x;
  fails <- inferProgramIO defaultDriverState (MkModuleName "fails") $ take 3 fun
  guard (isLeft fails)

  let decls = take 3 fun
  --  let action :: DriverM TST.Program
  let action :: DriverM TST.Program
      action = do
          st <- createSymbolTable (MkModuleName "action") decls
          addSymboltable (MkModuleName "This") st
          sts <- getSymbolTables
          resolvedDecls <- liftEitherErr (runResolverM sts (resolveProgram decls))
          let desugared = desugarProgram resolvedDecls
          rs <- sequence $ inferDecl (MkModuleName "action") <$> take 2 desugared
          return rs
          --  inferProgram mn (desugarProgram resolvedDecls)
  Right progWorks <- (fst <$>) <$> execDriverM defaultDriverState action
  return progWorks
  --  Right env <- (drvEnv . snd <$>) <$> execDriverM defaultDriverState action
  --  return env


