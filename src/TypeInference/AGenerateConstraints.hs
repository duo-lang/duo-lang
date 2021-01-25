module TypeInference.AGenerateConstraints
  ( agenerateConstraints
  ) where

import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Except

import Syntax.ATerms
import Syntax.Types
import Syntax.Program
import Utils

---------------------------------------------------------------------------------------------
-- State of GenM
---------------------------------------------------------------------------------------------

data GenerateState = GenerateState
  { varCount :: Int
  , constraints :: [Constraint]
  }

initialState :: GenerateState
initialState = GenerateState { varCount = 0, constraints = [] }

stateToConstraintSet :: GenerateState -> ConstraintSet
stateToConstraintSet GenerateState {..} = ConstraintSet
  { cs_constraints = constraints
  , cs_uvars = (\i -> MkTVar (show i)) <$> [0..varCount]
  }
---------------------------------------------------------------------------------------------
-- Reader of GenM
---------------------------------------------------------------------------------------------

data GenerateReader = GenerateReader { context :: [[SimpleType]]
                                     , env :: Environment
                                     }

initialReader :: Environment -> GenerateReader
initialReader env = GenerateReader { context = []
                                   , env = env
                                   }

---------------------------------------------------------------------------------------------
-- GenM
---------------------------------------------------------------------------------------------

type GenM a = ReaderT GenerateReader (StateT GenerateState (Except Error)) a

runGenM :: Environment -> GenM a -> Either Error (a, ConstraintSet)
runGenM env m = case runExcept (runStateT (runReaderT  m (initialReader env)) initialState) of
  Left err -> Left err
  Right (x, state) -> Right (x, stateToConstraintSet state)

---------------------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------------------

freshTVar :: GenM SimpleType
freshTVar = do
  var <- gets varCount
  modify (\gs@GenerateState{} -> gs { varCount = var + 1 })
  return (TyVar Normal (MkTVar (show var)))

lookupType :: Index -> GenM SimpleType
lookupType (i,j) = do
  ctx <- asks context
  return $ (ctx !! i) !! j

addConstraint :: Constraint -> GenM ()
addConstraint c = modify (\gs@GenerateState { constraints } -> gs { constraints = c:constraints })

---------------------------------------------------------------------------------------------
-- Constraint generation
---------------------------------------------------------------------------------------------

genConstraints :: ATerm () -> GenM (ATerm SimpleType, SimpleType)
genConstraints (BVar idx) = do
  ty <- lookupType idx
  return (BVar idx, ty)
genConstraints (FVar fv) = throwError $ GenConstraintsError $ "Free type var: " ++ fv
genConstraints (Ctor xt args) = do
  args' <- sequence (genConstraints <$> args)
  let ty = TySimple Data [MkXtorSig xt (Twice (snd <$> args') [])]
  return (Ctor xt (fst <$> args'), ty)
genConstraints (Dtor xt t args) = do
  args' <- sequence (genConstraints <$> args)
  retType <- freshTVar
  let codataType = TySimple Codata [MkXtorSig xt (Twice (snd <$> args') [retType])]
  (t', ty') <- genConstraints t
  addConstraint (SubType ty' codataType)
  return (Dtor xt t' (fst <$> args'), retType)
genConstraints (Match t cases) = do
  (t', matchType) <- genConstraints t
  retType <- freshTVar
  cases' <- sequence (genConstraintsCase retType <$> cases)
  addConstraint (SubType matchType (TySimple Data (snd <$> cases')))
  return (Match t' (fst <$> cases'), retType)
genConstraints (Comatch cocases) = do
  cocases' <- sequence (genConstraintsCocase <$> cocases)
  let ty = TySimple Codata (snd <$> cocases')
  return (Comatch (fst <$> cocases'), ty)

genConstraintsCase :: SimpleType -> ACase () -> GenM (ACase SimpleType, XtorSig SimpleType)
genConstraintsCase retType (MkACase { acase_name, acase_args, acase_term }) = do
  argts <- forM acase_args (\_ -> freshTVar)
  (acase_term', retTypeInf) <- local (\gr@GenerateReader{..} -> gr { context = argts:context }) (genConstraints acase_term)
  addConstraint (SubType retTypeInf retType)
  return (MkACase acase_name argts acase_term', MkXtorSig acase_name (Twice argts []))

genConstraintsCocase :: ACase () -> GenM (ACase SimpleType, XtorSig SimpleType)
genConstraintsCocase (MkACase { acase_name, acase_args, acase_term }) = do
  argts <- forM acase_args (\_ -> freshTVar)
  (acase_term', retType) <- local (\gr@GenerateReader{..} -> gr { context = argts:context }) (genConstraints acase_term)
  let sig = MkXtorSig acase_name (Twice argts [retType])
  return (MkACase acase_name argts acase_term', sig)



agenerateConstraints :: ATerm () -> Environment -> Either Error ((ATerm SimpleType, SimpleType), ConstraintSet)
agenerateConstraints tm env = do
  runGenM env (genConstraints tm)

