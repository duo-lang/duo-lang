module TypeInference.GenerateConstraints.ATerms where

import Control.Monad.Reader
import Control.Monad.Except

import Syntax.ATerms
import Syntax.Types
import Syntax.Program (Environment)
import Utils
import TypeInference.GenerateConstraints.Definition
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

