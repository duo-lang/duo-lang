module Renamer.Definition where

import Control.Monad.Except (throwError)
import Control.Monad.State
import Data.Map (Map)
import Data.Text qualified as T
import System.FilePath ( (</>), (<.>))
import System.Directory ( doesFileExist )

import Driver.Definition
import Driver.Environment
import Syntax.Common
import Utils
import Errors

type RenamerM a = DriverM a

getDriverEnv :: RenamerM (Environment Inferred)
getDriverEnv = gets driverEnv

getXtorMap :: RenamerM (Map (XtorName, DataCodata) (NominalStructural, Arity))
getXtorMap = gets (xtorMap . driverEnv)

setEnvironment :: Environment Inferred -> RenamerM ()
setEnvironment env = modify (\state -> state { driverEnv = env })

-- | Given the Library Paths contained in the inference options and a module name,
-- try to find a filepath which corresponds to the given module name.
findModule :: ModuleName -> Loc ->  RenamerM FilePath
findModule (MkModuleName mod) loc = do
  infopts <- gets driverOpts
  let libpaths = infOptsLibPath infopts
  fps <- forM libpaths $ \libpath -> do
    let fp = libpath </> T.unpack mod <.> "ds"
    exists <- liftIO $ doesFileExist fp
    if exists then return [fp] else return []
  case concat fps of
    [] -> throwError $ OtherError (Just loc) ("Could not locate library: " <> mod)
    (fp:_) -> return fp