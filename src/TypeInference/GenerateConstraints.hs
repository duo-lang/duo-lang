module TypeInference.GenerateConstraints
  ( sgenerateConstraints
  , agenerateConstraints
  ) where

import qualified Data.Map as M
import Control.Monad.Reader
import Control.Monad.Except
import Control.Monad.State


import Pretty.Pretty
import Syntax.ATerms
import Syntax.STerms
import Syntax.Types
import Syntax.Program (Environment)
import qualified Syntax.Program as P
import Utils

---------------------------------------------------------------------------------------------
-- State of GenM
--
-- We use varCount for generating fresh type variables, and collect the constraints.
---------------------------------------------------------------------------------------------

data GenerateState = GenerateState
  { varCount :: Int
  , constraints :: [Constraint]
  }

initialState :: GenerateState
initialState = GenerateState { varCount = 0, constraints = [] }

-- | After constraint generation is finished, we can turn the final state into a ConstraintSet.
stateToConstraintSet :: GenerateState -> ConstraintSet
stateToConstraintSet GenerateState {..} = ConstraintSet
  { cs_constraints = constraints
  , cs_uvars = (\i -> MkTVar (show i)) <$> [0..varCount]
  }

---------------------------------------------------------------------------------------------
-- Reader of GenM
--
-- We have access to a program environment and a local variable context.
---------------------------------------------------------------------------------------------

data GenerateReader = GenerateReader { context :: [TypArgs Pos]
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

-- | Generate a fresh type variable.
freshTVar :: GenM (Typ Pos)
freshTVar = do
  var <- gets varCount
  modify (\gs@GenerateState{} -> gs { varCount = var + 1 })
  return (TyVar PosRep Normal (MkTVar (show var)))

freshTVars :: Twice [()] -> GenM (TypArgs Pos)
freshTVars (Twice prdArgs cnsArgs) = do
  prdArgs' <- forM prdArgs (\_ -> freshTVar)
  cnsArgs' <- forM cnsArgs (\_ -> freshTVar)
  return (MkTypArgs prdArgs' cnsArgs')

-- | Lookup a type of a bound variable in the context.
lookupType :: PrdCnsRep pc -> Index -> GenM (Typ Pos)
lookupType PrdRep (i,j) = do
  ctx <- asks context
  let (MkTypArgs { prdTypes }) = ctx !! i
  return $ prdTypes !! j
lookupType CnsRep (i,j) = do
  ctx <- asks context
  let (MkTypArgs { cnsTypes }) = ctx !! i
  return $ cnsTypes !! j

-- | Add a constraint to the state.
addConstraint :: Constraint -> GenM ()
addConstraint c = modify (\gs@GenerateState { constraints } -> gs { constraints = c:constraints })

lookupCase :: XtorName -> GenM (TypArgs Pos, XtorArgs (Typ Pos))
lookupCase xt = do
  env <- asks env
  case M.lookup xt (P.envToXtorMap env) of
    Nothing -> throwError $ GenConstraintsError ("GenerateConstraints: The xtor " ++ ppPrint xt ++ " could not be looked up.")
    Just types@(MkTypArgs prdTypes cnsTypes) -> do
      let prds = (\ty -> FreeVar PrdRep "y" ty) <$> prdTypes
      let cnss = (\ty -> FreeVar CnsRep "y" ty) <$> cnsTypes
      return (types, MkXtorArgs prds cnss)

lookupXtor :: XtorName -> GenM DataDecl
lookupXtor xt = do
  env <- asks env
  case P.lookupXtor xt env of
    Nothing -> throwError $ GenConstraintsError ("Constructor " ++ ppPrint xt ++ " is not contained in program")
    Just decl -> return decl

---------------------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------------------

isContainedIn :: XtorName -> [XtorSig Pos] -> GenM ()
isContainedIn xt xtors =
  if or (isContainedIn' <$> xtors)
  then return ()
  else throwError $ GenConstraintsError ("Pattern match fail with xtor" ++ ppPrint xt)
    where
      isContainedIn' :: XtorSig Pos -> Bool
      isContainedIn' MkXtorSig { sig_name } | xt == sig_name = True
                                            | otherwise      = False

genConstraintsArgs :: XtorArgs () -> GenM (XtorArgs (Typ Pos), TypArgs Pos)
genConstraintsArgs (MkXtorArgs prdArgs cnsArgs) = do
  prdArgs' <- forM prdArgs genConstraintsSTerm
  cnsArgs' <- forM cnsArgs genConstraintsSTerm
  return (MkXtorArgs (fst <$> prdArgs') (fst <$> cnsArgs'), MkTypArgs (snd <$> prdArgs') (snd <$> cnsArgs'))

genConstraintsSTerm :: STerm pc () -> GenM (STerm pc (Typ Pos), (Typ Pos))
genConstraintsSTerm (BoundVar rep idx) = do
  ty <- lookupType rep idx
  return (BoundVar rep idx, ty)
genConstraintsSTerm (FreeVar _ _ _) = throwError $ GenConstraintsError "Should not occur"
genConstraintsSTerm (XtorCall PrdRep xt@(MkXtorName { xtorNominalStructural = Structural }) args) = do
  (args', argTypes) <- genConstraintsArgs args
  return (XtorCall PrdRep xt args', TyStructural PosRep DataRep [MkXtorSig xt argTypes])
genConstraintsSTerm (XtorCall CnsRep xt@(MkXtorName { xtorNominalStructural = Structural }) args) = do
  (args', argTypes) <- genConstraintsArgs args
  return (XtorCall CnsRep xt args', TyStructural PosRep CodataRep [MkXtorSig xt argTypes])
genConstraintsSTerm (XtorCall rep xt@(MkXtorName { xtorNominalStructural = Nominal }) args) = do
  (args', _argTypes) <- genConstraintsArgs args
  tn <- lookupXtor xt
  -- TODO: Check if args of xtor are correct?
  return (XtorCall rep xt args', TyNominal PosRep (data_name tn))
genConstraintsSTerm (XMatch PrdRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      fvars <- freshTVars scase_args
                      cmd' <- local (\gr@GenerateReader{..} -> gr { context = fvars:context }) (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name (demote fvars) cmd', MkXtorSig scase_name fvars))
  return (XMatch PrdRep Structural (fst <$> cases'), TyStructural PosRep CodataRep (snd <$> cases'))
genConstraintsSTerm (XMatch CnsRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      fvars <- freshTVars scase_args
                      cmd' <- local (\gr@GenerateReader{..} -> gr { context = fvars:context }) (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name (demote fvars) cmd', MkXtorSig scase_name fvars))
  return (XMatch CnsRep Structural (fst <$> cases'), TyStructural PosRep DataRep (snd <$> cases'))
-- We know that empty matches cannot be parsed as nominal, so it is save to take the head of the xtors.
genConstraintsSTerm (XMatch _ Nominal []) = throwError $ GenConstraintsError "Unreachable"
genConstraintsSTerm (XMatch rep Nominal (pmcase:pmcases)) = do
  tn <- lookupXtor (scase_name pmcase)
  cases' <- forM (pmcase:pmcases) (\MkSCase {..} -> do
                                      scase_name `isContainedIn` (data_xtors tn)
                                      (x,_) <- lookupCase scase_name
                                      cmd' <- local (\gr@GenerateReader{..} -> gr { context = x:context }) (genConstraintsCommand scase_cmd)
                                      return (MkSCase scase_name (demote x) cmd'))
  return (XMatch rep Nominal cases', TyNominal PosRep (data_name tn))
genConstraintsSTerm (MuAbs PrdRep () cmd) = do
  fv <- freshTVar
  cmd' <- local (\gr@GenerateReader{..} -> gr { context = (MkTypArgs [] [fv]):context }) (genConstraintsCommand cmd)
  return (MuAbs PrdRep fv cmd', fv)
genConstraintsSTerm (MuAbs CnsRep () cmd) = do
  fv <- freshTVar
  cmd' <- local (\gr@GenerateReader{..} -> gr { context = (MkTypArgs [fv] []):context }) (genConstraintsCommand cmd)
  return (MuAbs CnsRep fv cmd', fv)

genConstraintsCommand :: Command () -> GenM (Command (Typ Pos))
genConstraintsCommand Done = return Done
genConstraintsCommand (Print t) = do
  (t',_) <- genConstraintsSTerm t
  return (Print t')
genConstraintsCommand (Apply t1 t2) = do
  (t1',ty1) <- genConstraintsSTerm t1
  (t2',ty2) <- genConstraintsSTerm t2
  addConstraint (SubType ty1 ty2)
  return (Apply t1' t2')

sgenerateConstraints :: STerm pc ()
                      -> Environment
                      -> Either Error ((STerm pc (Typ Pos), Typ Pos), ConstraintSet)
sgenerateConstraints tm env = runGenM env (genConstraintsSTerm tm)

---------------------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------------------

genConstraintsATerm :: ATerm () -> GenM (ATerm (Typ Pos), Typ Pos)
genConstraintsATerm (BVar idx) = do
  ty <- lookupType PrdRep idx
  return (BVar idx, ty)
genConstraintsATerm (FVar fv) = throwError $ GenConstraintsError $ "Free type var: " ++ fv
genConstraintsATerm (Ctor xt args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  let ty = TyStructural PosRep DataRep [MkXtorSig xt (MkTypArgs (snd <$> args') [])]
  return (Ctor xt (fst <$> args'), ty)
genConstraintsATerm (Dtor xt t args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  retType <- freshTVar
  let codataType = TyStructural PosRep CodataRep [MkXtorSig xt (MkTypArgs (snd <$> args') [retType])]
  (t', ty') <- genConstraintsATerm t
  addConstraint (SubType ty' codataType)
  return (Dtor xt t' (fst <$> args'), retType)
genConstraintsATerm (Match t cases) = do
  (t', matchType) <- genConstraintsATerm t
  retType <- freshTVar
  cases' <- sequence (genConstraintsATermCase retType <$> cases)
  addConstraint (SubType matchType (TyStructural PosRep DataRep (snd <$> cases')))
  return (Match t' (fst <$> cases'), retType)
genConstraintsATerm (Comatch cocases) = do
  cocases' <- sequence (genConstraintsATermCocase <$> cocases)
  let ty = TyStructural PosRep CodataRep (snd <$> cocases')
  return (Comatch (fst <$> cocases'), ty)

genConstraintsATermCase :: Typ Pos -> ACase () -> GenM (ACase (Typ Pos), XtorSig Pos)
genConstraintsATermCase retType (MkACase { acase_name, acase_args, acase_term }) = do
  argts <- forM acase_args (\_ -> freshTVar)
  (acase_term', retTypeInf) <- local (\gr@GenerateReader{..} -> gr { context = (MkTypArgs argts []):context }) (genConstraintsATerm acase_term)
  addConstraint (SubType retTypeInf retType)
  return (MkACase acase_name argts acase_term', MkXtorSig acase_name (MkTypArgs argts []))

genConstraintsATermCocase :: ACase () -> GenM (ACase (Typ Pos), XtorSig Pos)
genConstraintsATermCocase (MkACase { acase_name, acase_args, acase_term }) = do
  argts <- forM acase_args (\_ -> freshTVar)
  (acase_term', retType) <- local (\gr@GenerateReader{..} -> gr { context = (MkTypArgs argts []):context }) (genConstraintsATerm acase_term)
  let sig = MkXtorSig acase_name (MkTypArgs argts [retType])
  return (MkACase acase_name argts acase_term', sig)

agenerateConstraints :: ATerm () -> Environment -> Either Error ((ATerm (Typ Pos), Typ Pos), ConstraintSet)
agenerateConstraints tm env = runGenM env (genConstraintsATerm tm)
