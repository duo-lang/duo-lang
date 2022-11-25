module Eval.Definition where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Map (Map)
import Data.Map qualified as M
import Data.List (find)
import Data.List.NonEmpty (NonEmpty)
import Text.Read (readMaybe)

import Errors
import Pretty.Pretty
import Pretty.Terms ()
import Syntax.CST.Names
import Syntax.CST.Kinds
import Syntax.Core.Annot
import Syntax.Core.Terms (Pattern(..))
import Syntax.TST.Terms
import Loc
import Syntax.TST.Types qualified as TST
import Syntax.RST.Types (Polarity(..), PolarityRep(..))
import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Control.Monad.Writer (MonadWriter)
import Control.Monad.State (MonadState)

---------------------------------------------------------------------------------
-- The Eval Monad
---------------------------------------------------------------------------------

type EvalEnv = (Map FreeVarName (Term Prd), Map FreeVarName (Term Cns), Map FreeVarName Command)

newtype EvalM m a = EvalM { unEvalM :: ReaderT EvalEnv (ExceptT (NonEmpty Error) m) a }
  deriving newtype (Functor, Applicative, Monad, MonadWriter w, MonadState s, MonadError (NonEmpty Error), MonadReader EvalEnv, MonadIO)

runEval :: EvalM m a -> EvalEnv -> m (Either (NonEmpty Error) a)
runEval e env = runExceptT (runReaderT (unEvalM e) env)

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

lookupMatchCase :: Monad m => XtorName -> [CmdCase] -> EvalM m CmdCase
lookupMatchCase xt cases = case find (\MkCmdCase { cmdcase_pat = XtorPat _ xt' _ } -> xt == xt') cases of
  Just pmcase -> return pmcase
  Nothing -> throwEvalError defaultLoc ["Error during evaluation. The xtor: "
                                       , unXtorName xt
                                       , "doesn't occur in match."
                                       ]

checkArgs :: Monad m => Command -> [(PrdCns,a)] -> Substitution -> EvalM m ()
checkArgs cmd args (MkSubstitution subst) = checkArgs' args subst
  where
    checkArgs' [] [] = return ()
    checkArgs' ((Prd,_):rest1) (PrdTerm _:rest2) = checkArgs' rest1 rest2
    checkArgs' ((Cns,_):rest1) (CnsTerm _:rest2) = checkArgs' rest1 rest2
    checkArgs' _ _ = throwEvalError defaultLoc [ "Error during evaluation of:"
                                                  ,  ppPrint cmd
                                                  , "Argument lengths don't coincide."
                                                  ]

natType :: TST.Typ 'Pos
natType = TST.TyNominal defaultLoc PosRep (MkPolyKind [] CBV) peanoNm

convertInt :: Int -> Term Prd
convertInt 0 = Xtor defaultLoc XtorAnnotOrig PrdRep natType CST.Nominal (MkXtorName "Z") $ MkSubstitution []
convertInt n = Xtor defaultLoc XtorAnnotOrig PrdRep natType CST.Nominal (MkXtorName "S") $ MkSubstitution [PrdTerm $ convertInt (n-1)]


readInt :: IO (Term Prd)
readInt = do
  putStrLn "Enter a positive integer:"
  input <- getLine
  case readMaybe input of
    Nothing        -> putStrLn "Incorrect input." >> readInt
    Just i | i < 0 -> putStrLn "Incorrect input." >> readInt
    Just i         -> pure (convertInt i)

lookupCommand :: Monad m => FreeVarName -> EvalM m Command
lookupCommand fv = do
  (_,_,env) <- ask
  case M.lookup fv env of
    Nothing -> throwEvalError defaultLoc ["Consumer " <> ppPrint fv <> " not in environment."]
    Just cmd -> pure cmd

lookupTerm :: Monad m => PrdCnsRep pc -> FreeVarName -> EvalM m (Term pc)
lookupTerm PrdRep fv = do
  (env,_,_) <- ask
  case M.lookup fv env of
    Nothing -> throwEvalError defaultLoc ["Producer " <> ppPrint fv <> " not in environment."]
    Just prd -> pure prd
lookupTerm CnsRep fv = do
  (_,env,_) <- ask
  case M.lookup fv env of
    Nothing -> throwEvalError defaultLoc ["Consumer " <> ppPrint fv <> " not in environment."]
    Just prd -> pure prd
