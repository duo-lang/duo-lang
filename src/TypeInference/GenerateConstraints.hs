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

data GenerateReader = GenerateReader { context :: [Twice [SimpleType]]
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

freshTVars :: Twice [()] -> GenM (Twice [SimpleType])
freshTVars (Twice prdArgs cnsArgs) = do
  prdArgs' <- forM prdArgs (\_ -> freshTVar)
  cnsArgs' <- forM cnsArgs (\_ -> freshTVar)
  return (Twice prdArgs' cnsArgs')

lookupPrdType :: Index -> GenM SimpleType
lookupPrdType (i,j) = do
  ctx <- asks context
  let (Twice prdTypes _) = ctx !! i
  return $ prdTypes !! j

lookupCnsType :: Index -> GenM SimpleType
lookupCnsType (i,j) = do
  ctx <- asks context
  let (Twice _ cnsTypes) = ctx !! i
  return $ cnsTypes !! j

addConstraint :: Constraint -> GenM ()
addConstraint c = modify (\gs@GenerateState { constraints } -> gs { constraints = c:constraints })

lookupCase :: XtorName -> GenM (Twice [SimpleType], XtorArgs SimpleType)
lookupCase xt = do
  env <- asks env
  case M.lookup xt (P.envToXtorMap env) of
    Nothing -> throwError $ GenConstraintsError ("GenerateConstraints: The xtor " ++ ppPrint xt ++ " could not be looked up.")
    Just types@(Twice prdTypes cnsTypes) -> do
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

isContainedIn :: XtorName -> [XtorSig SimpleType] -> GenM ()
isContainedIn xt xtors =
  if or (isContainedIn' <$> xtors)
  then return ()
  else throwError $ GenConstraintsError ("Pattern match fail with xtor" ++ ppPrint xt)
    where
      isContainedIn' :: XtorSig SimpleType -> Bool
      isContainedIn' MkXtorSig { sig_name } | xt == sig_name = True
                                            | otherwise      = False

genConstraintsArgs :: XtorArgs () -> GenM (XtorArgs SimpleType, Twice [SimpleType])
genConstraintsArgs (MkXtorArgs prdArgs cnsArgs) = do
  prdArgs' <- forM prdArgs genConstraintsSTerm
  cnsArgs' <- forM cnsArgs genConstraintsSTerm
  return (MkXtorArgs (fst <$> prdArgs') (fst <$> cnsArgs'), Twice (snd <$> prdArgs') (snd <$> cnsArgs'))

genConstraintsSTerm :: STerm pc () -> GenM (STerm pc SimpleType, SimpleType)
genConstraintsSTerm (BoundVar PrdRep idx) = do
  ty <- lookupPrdType idx
  return (BoundVar PrdRep idx, ty)
genConstraintsSTerm (BoundVar CnsRep idx) = do
  ty <- lookupCnsType idx
  return (BoundVar CnsRep idx, ty)
genConstraintsSTerm (FreeVar _ _ _) = throwError $ GenConstraintsError "Should not occur"
genConstraintsSTerm (XtorCall PrdRep xt@(MkXtorName { xtorNominalStructural = Structural }) args) = do
  (args', argTypes) <- genConstraintsArgs args
  return (XtorCall PrdRep xt args', TySimple Data [MkXtorSig xt argTypes])
genConstraintsSTerm (XtorCall CnsRep xt@(MkXtorName { xtorNominalStructural = Structural }) args) = do
  (args', argTypes) <- genConstraintsArgs args
  return (XtorCall CnsRep xt args', TySimple Codata [MkXtorSig xt argTypes])
genConstraintsSTerm (XtorCall rep xt@(MkXtorName { xtorNominalStructural = Nominal }) args) = do
  (args', _argTypes) <- genConstraintsArgs args
  tn <- lookupXtor xt
  -- TODO: Check if args of xtor are correct?
  return (XtorCall rep xt args', TyNominal (data_name tn))
genConstraintsSTerm (XMatch PrdRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      fvars <- freshTVars scase_args
                      cmd' <- local (\gr@GenerateReader{..} -> gr { context = fvars:context }) (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name fvars cmd', MkXtorSig scase_name fvars))
  return (XMatch PrdRep Structural (fst <$> cases'), TySimple Codata (snd <$> cases'))
genConstraintsSTerm (XMatch CnsRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      fvars <- freshTVars scase_args
                      cmd' <- local (\gr@GenerateReader{..} -> gr { context = fvars:context }) (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name fvars cmd', MkXtorSig scase_name fvars))
  return (XMatch CnsRep Structural (fst <$> cases'), TySimple Data (snd <$> cases'))
-- We know that empty matches cannot be parsed as nominal, so it is save to take the head of the xtors.
genConstraintsSTerm (XMatch _ Nominal []) = throwError $ GenConstraintsError "Unreachable"
genConstraintsSTerm (XMatch rep Nominal (pmcase:pmcases)) = do
  tn <- lookupXtor (scase_name pmcase)
  cases' <- forM (pmcase:pmcases) (\MkSCase {..} -> do
                                      scase_name `isContainedIn` (data_xtors tn)
                                      (x,y) <- lookupCase scase_name
                                      cmd' <- local (\gr@GenerateReader{..} -> gr { context = x:context }) (genConstraintsCommand scase_cmd)
                                      return (MkSCase scase_name x cmd'))
  return (XMatch rep Nominal cases', TyNominal (data_name tn))
genConstraintsSTerm (MuAbs PrdRep () cmd) = do
  fv <- freshTVar
  cmd' <- local (\gr@GenerateReader{..} -> gr { context = (Twice [] [fv]):context }) (genConstraintsCommand cmd)
  return (MuAbs PrdRep fv cmd', fv)
genConstraintsSTerm (MuAbs CnsRep () cmd) = do
  fv <- freshTVar
  cmd' <- local (\gr@GenerateReader{..} -> gr { context = (Twice [fv] []):context }) (genConstraintsCommand cmd)
  return (MuAbs CnsRep fv cmd', fv)

genConstraintsCommand :: Command () -> GenM (Command SimpleType)
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
                      -> Either Error ((STerm pc SimpleType, SimpleType), ConstraintSet)
sgenerateConstraints tm env = runGenM env (genConstraintsSTerm tm)

---------------------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------------------

genConstraintsATerm :: ATerm () -> GenM (ATerm SimpleType, SimpleType)
genConstraintsATerm (BVar idx) = do
  ty <- lookupPrdType idx
  return (BVar idx, ty)
genConstraintsATerm (FVar fv) = throwError $ GenConstraintsError $ "Free type var: " ++ fv
genConstraintsATerm (Ctor xt args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  let ty = TySimple Data [MkXtorSig xt (Twice (snd <$> args') [])]
  return (Ctor xt (fst <$> args'), ty)
genConstraintsATerm (Dtor xt t args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  retType <- freshTVar
  let codataType = TySimple Codata [MkXtorSig xt (Twice (snd <$> args') [retType])]
  (t', ty') <- genConstraintsATerm t
  addConstraint (SubType ty' codataType)
  return (Dtor xt t' (fst <$> args'), retType)
genConstraintsATerm (Match t cases) = do
  (t', matchType) <- genConstraintsATerm t
  retType <- freshTVar
  cases' <- sequence (genConstraintsATermCase retType <$> cases)
  addConstraint (SubType matchType (TySimple Data (snd <$> cases')))
  return (Match t' (fst <$> cases'), retType)
genConstraintsATerm (Comatch cocases) = do
  cocases' <- sequence (genConstraintsATermCocase <$> cocases)
  let ty = TySimple Codata (snd <$> cocases')
  return (Comatch (fst <$> cocases'), ty)

genConstraintsATermCase :: SimpleType -> ACase () -> GenM (ACase SimpleType, XtorSig SimpleType)
genConstraintsATermCase retType (MkACase { acase_name, acase_args, acase_term }) = do
  argts <- forM acase_args (\_ -> freshTVar)
  (acase_term', retTypeInf) <- local (\gr@GenerateReader{..} -> gr { context = (Twice argts []):context }) (genConstraintsATerm acase_term)
  addConstraint (SubType retTypeInf retType)
  return (MkACase acase_name argts acase_term', MkXtorSig acase_name (Twice argts []))

genConstraintsATermCocase :: ACase () -> GenM (ACase SimpleType, XtorSig SimpleType)
genConstraintsATermCocase (MkACase { acase_name, acase_args, acase_term }) = do
  argts <- forM acase_args (\_ -> freshTVar)
  (acase_term', retType) <- local (\gr@GenerateReader{..} -> gr { context = (Twice argts []):context }) (genConstraintsATerm acase_term)
  let sig = MkXtorSig acase_name (Twice argts [retType])
  return (MkACase acase_name argts acase_term', sig)

agenerateConstraints :: ATerm () -> Environment -> Either Error ((ATerm SimpleType, SimpleType), ConstraintSet)
agenerateConstraints tm env = runGenM env (genConstraintsATerm tm)
