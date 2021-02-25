module TypeInference.GenerateConstraints
  ( sgenerateConstraints
  , agenerateConstraints
  , sgenerateConstraintsCmd
  , PrdCnsToPol
  , prdCnsToPol
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
freshTVar :: GenM (Typ Pos, Typ Neg)
freshTVar = do
  var <- gets varCount
  modify (\gs@GenerateState{} -> gs { varCount = var + 1 })
  return (TyVar PosRep Normal (MkTVar (show var))
         ,TyVar NegRep Normal (MkTVar (show var)))

freshTVars :: Twice [()] -> GenM (TypArgs Pos, TypArgs Neg)
freshTVars (Twice prdArgs cnsArgs) = do
  (prdArgsPos, prdArgsNeg) <- unzip <$> forM prdArgs (\_ -> freshTVar)
  (cnsArgsPos, cnsArgsNeg) <- unzip <$> forM cnsArgs (\_ -> freshTVar)
  return (MkTypArgs prdArgsPos cnsArgsNeg, MkTypArgs prdArgsNeg cnsArgsPos)

-- | We map producer terms to positive types, and consumer terms to negative types.
type family PrdCnsToPol (pc :: PrdCns) :: Polarity where
  PrdCnsToPol Prd = Pos
  PrdCnsToPol Cns = Neg

prdCnsToPol :: PrdCnsRep pc -> PolarityRep (PrdCnsToPol pc)
prdCnsToPol PrdRep = PosRep
prdCnsToPol CnsRep = NegRep

foo :: PrdCnsRep pc -> PolarityRep (PrdCnsToPol pc)
foo PrdRep = PosRep
foo CnsRep = NegRep

-- | Lookup a type of a bound variable in the context.
lookupType :: PrdCnsRep pc -> Index -> GenM (Typ (PrdCnsToPol pc))
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

lookupCase :: XtorName -> GenM (TypArgs Pos, XtorArgs ())
lookupCase xt = do
  env <- asks env
  case M.lookup xt (P.envToXtorMap env) of
    Nothing -> throwError $ GenConstraintsError ("GenerateConstraints: The xtor " ++ ppPrint xt ++ " could not be looked up.")
    Just types@(MkTypArgs prdTypes cnsTypes) -> do
      let prds = (\_ -> FreeVar PrdRep "y" ()) <$> prdTypes
      let cnss = (\_ -> FreeVar CnsRep "y" ()) <$> cnsTypes
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

-- | Checks for a given list of XtorNames and a type declaration whether:
-- (1) All the xtornames occur in the type declaration. (Correctness)
-- (2) All xtors of the type declaration are matched against. (Exhaustiveness)
checkExhaustiveness :: [XtorName] -- ^ The xtor names used in the pattern match
                    -> DataDecl   -- ^ The type declaration to check against.
                    -> GenM ()
checkExhaustiveness matched decl = do
  let declared = sig_name <$> (data_xtors decl)
  forM_ matched $ \xn -> when (not (xn `elem` declared)) (throwError $ GenConstraintsError ("Pattern Match Error. The xtor " ++ ppPrint xn ++ " does not occur in the declaration of type " ++ ppPrint (data_name decl)))
  forM_ declared $ \xn -> when (not (xn `elem` matched)) (throwError $ GenConstraintsError ("Pattern Match Exhaustiveness Error. Xtor: " ++ ppPrint xn ++ " of type " ++ ppPrint (data_name decl) ++ " is not matched against." ))

genConstraintsArgs :: XtorArgs () -> GenM (XtorArgs (), TypArgs Pos)
genConstraintsArgs (MkXtorArgs prdArgs cnsArgs) = do
  prdArgs' <- forM prdArgs genConstraintsSTerm
  cnsArgs' <- forM cnsArgs genConstraintsSTerm
  return (MkXtorArgs (fst <$> prdArgs') (fst <$> cnsArgs'), MkTypArgs (snd <$> prdArgs') (snd <$> cnsArgs'))

genConstraintsSTerm :: STerm pc () -> GenM (STerm pc (), Typ (PrdCnsToPol pc))
genConstraintsSTerm (BoundVar rep idx) = do
  ty <- lookupType rep idx
  return (BoundVar rep idx, ty)
genConstraintsSTerm (FreeVar _ _ _) = throwError $ GenConstraintsError "Should not occur"
genConstraintsSTerm (XtorCall PrdRep xt@(MkXtorName { xtorNominalStructural = Structural }) args) = do
  (args', argTypes) <- genConstraintsArgs args
  return (XtorCall PrdRep xt args', TyStructural PosRep DataRep [MkXtorSig xt argTypes])
genConstraintsSTerm (XtorCall CnsRep xt@(MkXtorName { xtorNominalStructural = Structural }) args) = do
  (args', argTypes) <- genConstraintsArgs args
  return (XtorCall CnsRep xt args', TyStructural NegRep CodataRep [MkXtorSig xt argTypes])
genConstraintsSTerm (XtorCall rep xt@(MkXtorName { xtorNominalStructural = Nominal }) args) = do
  (args', _argTypes) <- genConstraintsArgs args
  tn <- lookupXtor xt
  -- TODO: Check if args of xtor are correct?
  return (XtorCall rep xt args', TyNominal (foo rep) (data_name tn))
genConstraintsSTerm (XMatch PrdRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      (fvarsPos, fvarsNeg) <- freshTVars scase_args
                      cmd' <- local (\gr@GenerateReader{..} -> gr { context = fvarsPos:context }) (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  return (XMatch PrdRep Structural (fst <$> cases'), TyStructural PosRep CodataRep (snd <$> cases'))
genConstraintsSTerm (XMatch CnsRep Structural cases) = do
  cases' <- forM cases (\MkSCase{..} -> do
                      (fvarsPos, fvarsNeg) <- freshTVars scase_args
                      cmd' <- local (\gr@GenerateReader{..} -> gr { context = fvarsPos:context }) (genConstraintsCommand scase_cmd)
                      return (MkSCase scase_name scase_args cmd', MkXtorSig scase_name fvarsNeg))
  return (XMatch CnsRep Structural (fst <$> cases'), TyStructural NegRep DataRep (snd <$> cases'))
-- We know that empty matches cannot be parsed as nominal, so it is save to take the head of the xtors.
genConstraintsSTerm (XMatch _ Nominal []) = throwError $ GenConstraintsError "Unreachable: A Match on a nominal type with 0 cases cannot be parsed."
genConstraintsSTerm (XMatch PrdRep Nominal cases@(pmcase:_)) = do
  tn <- lookupXtor (scase_name pmcase)
  checkExhaustiveness (scase_name <$> cases) tn
  cases' <- forM cases (\MkSCase {..} -> do
                           (x,_) <- lookupCase scase_name
                           cmd' <- local (\gr@GenerateReader{..} -> gr { context = x:context }) (genConstraintsCommand scase_cmd)
                           return (MkSCase scase_name scase_args cmd'))
  return (XMatch PrdRep Nominal cases', TyNominal PosRep (data_name tn))
genConstraintsSTerm (XMatch CnsRep Nominal cases@(pmcase:_)) = do
  tn <- lookupXtor (scase_name pmcase)
  checkExhaustiveness (scase_name <$> cases) tn
  cases' <- forM cases (\MkSCase {..} -> do
                           (x,_) <- lookupCase scase_name
                           cmd' <- local (\gr@GenerateReader{..} -> gr { context = x:context }) (genConstraintsCommand scase_cmd)
                           return (MkSCase scase_name undefined cmd'))
  return (XMatch CnsRep Nominal cases', TyNominal NegRep (data_name tn))
genConstraintsSTerm (MuAbs PrdRep () cmd) = do
  (fvpos, fvneg) <- freshTVar
  cmd' <- local (\gr@GenerateReader{..} -> gr { context = (MkTypArgs [] [fvneg]):context }) (genConstraintsCommand cmd)
  return (MuAbs PrdRep () cmd', fvpos)
genConstraintsSTerm (MuAbs CnsRep () cmd) = do
  (fvpos, fvneg) <- freshTVar
  cmd' <- local (\gr@GenerateReader{..} -> gr { context = (MkTypArgs [fvpos] []):context }) (genConstraintsCommand cmd)
  return (MuAbs CnsRep () cmd', fvneg)

genConstraintsCommand :: Command () -> GenM (Command ())
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
                      -> Either Error ((STerm pc (), Typ (PrdCnsToPol pc)), ConstraintSet)
sgenerateConstraints tm env = runGenM env (genConstraintsSTerm tm)

sgenerateConstraintsCmd :: Command () -> Environment -> Either Error ConstraintSet
sgenerateConstraintsCmd cmd env = snd <$> runGenM env (genConstraintsCommand cmd)

---------------------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------------------

-- | Every asymmetric terms gets assigned a positive type.
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
  (retTypePos, retTypeNeg) <- freshTVar
  let codataType = TyStructural NegRep CodataRep [MkXtorSig xt (MkTypArgs (snd <$> args') [retTypeNeg])]
  (t', ty') <- genConstraintsATerm t
  addConstraint (SubType ty' codataType)
  return (Dtor xt t' (fst <$> args'), retTypePos)
genConstraintsATerm (Match t cases) = do
  (t', matchType) <- genConstraintsATerm t
  (retTypePos, retTypeNeg) <- freshTVar
  cases' <- sequence (genConstraintsATermCase retTypeNeg <$> cases)
  addConstraint (SubType matchType (TyStructural NegRep DataRep (snd <$> cases')))
  return (Match t' (fst <$> cases'), retTypePos)
genConstraintsATerm (Comatch cocases) = do
  cocases' <- sequence (genConstraintsATermCocase <$> cocases)
  let ty = TyStructural PosRep CodataRep (snd <$> cocases')
  return (Comatch (fst <$> cocases'), ty)

genConstraintsATermCase :: Typ Neg -> ACase () -> GenM (ACase (Typ Pos), XtorSig Neg)
genConstraintsATermCase retType (MkACase { acase_name, acase_args, acase_term }) = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (\_ -> freshTVar)
  (acase_term', retTypeInf) <- local (\gr@GenerateReader{..} -> gr { context = (MkTypArgs argtsPos []):context }) (genConstraintsATerm acase_term)
  addConstraint (SubType retTypeInf retType)
  return (MkACase acase_name argtsPos acase_term', MkXtorSig acase_name (MkTypArgs argtsNeg []))

genConstraintsATermCocase :: ACase () -> GenM (ACase (Typ Pos), XtorSig Neg)
genConstraintsATermCocase (MkACase { acase_name, acase_args, acase_term }) = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (\_ -> freshTVar)
  (acase_term', retType) <- local (\gr@GenerateReader{..} -> gr { context = (MkTypArgs argtsPos []):context }) (genConstraintsATerm acase_term)
  let sig = MkXtorSig acase_name (MkTypArgs argtsNeg [retType])
  return (MkACase acase_name argtsPos acase_term', sig)

agenerateConstraints :: ATerm () -> Environment -> Either Error ((ATerm (Typ Pos), Typ Pos), ConstraintSet)
agenerateConstraints tm env = runGenM env (genConstraintsATerm tm)
