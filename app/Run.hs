module Run (runRun, desugarEnv) where

import Control.Monad.IO.Class (liftIO)
import Data.Map qualified as M

import Driver.Definition
import TypeInference.Environment
import Driver.Driver ( runCompilationModule )
import Eval.Definition (EvalEnv)
import Eval.Eval (eval)
import Syntax.CST.Names
import Syntax.CST.Types
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Translate.Focusing (Focus(..) )
import Loc ( defaultLoc )
import Options (DebugFlags(..))
import Pretty.Errors (printLocatedReport)

driverAction :: ModuleName -> DriverM TST.Module
driverAction mn = do
  runCompilationModule mn
  queryTypecheckedModule mn

desugarEnv :: Environment -> EvalEnv
desugarEnv env = (prd,cns,cmd,env.instanceDeclEnv)
  where
    prd = (\(tm,_,_) -> tm) <$> env.prdEnv
    cns = (\(tm,_,_) -> tm) <$> env.cnsEnv
    cmd = fst <$> env.cmdEnv

runRun :: DebugFlags -> Either FilePath ModuleName -> IO ()
runRun flags modId = 
  case modId of
    Left fp -> putStrLn $ "Please specify module name instead of filepath " ++ fp
    Right mn -> do
      (res, warnings) <- execDriverM driverState (driverAction mn)
      mapM_ printLocatedReport warnings
      case res of
        Left errs -> mapM_ printLocatedReport errs
        Right (_, state) -> do
          -- Run program
          let compiledEnv :: EvalEnv = focus CBV ((foldMap desugarEnv . M.elems) state.drvEnv)
          evalCmd <- liftIO $ eval (TST.Jump defaultLoc (MkFreeVarName "main")) compiledEnv
          case evalCmd of
              Left errs -> mapM_ printLocatedReport errs
              Right _res -> return ()
    where
      driverState = defaultDriverState { drvOpts = infOpts }
      infOpts = (if flags.df_printGraphs then setPrintGraphOpts else id) infOpts'
      infOpts' = (if flags.df_debug then setDebugOpts else id) defaultInferenceOptions

