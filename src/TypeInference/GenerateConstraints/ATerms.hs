module TypeInference.GenerateConstraints.ATerms
  ( genConstraintsATerm
  , genConstraintsATermRecursive
  ) where

import Control.Monad.Reader
import qualified Data.Map as M

import Pretty.Pretty
import Syntax.ATerms
import Syntax.Types
import Syntax.Program
import TypeInference.GenerateConstraints.Definition
import Utils

---------------------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------------------

-- | Every asymmetric terms gets assigned a positive type.
genConstraintsATerm :: ATerm Loc FreeVarName -> GenM (ATerm () FreeVarName, Typ Pos)
genConstraintsATerm (BVar _ idx) = do
  ty <- lookupType PrdRep idx
  return (BVar () idx, ty)
genConstraintsATerm (FVar _ fv) = do
  defEnv <- asks (defEnv . env)
  case M.lookup fv defEnv of
    Just (_,tys) -> do
      ty <- instantiateTypeScheme tys
      return (FVar () fv, ty)
    Nothing -> throwGenError $ "Unbound free producer variable in ATerm: " ++ ppPrint fv
genConstraintsATerm (Ctor _ xt args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  let ty = TyData PosRep [MkXtorSig xt (MkTypArgs (snd <$> args') [])]
  return (Ctor () xt (fst <$> args'), ty)
genConstraintsATerm (Dtor loc xt t args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  (retTypePos, retTypeNeg) <- freshTVar Other
  let codataType = TyCodata NegRep [MkXtorSig xt (MkTypArgs (snd <$> args') [retTypeNeg])]
  (t', ty') <- genConstraintsATerm t
  addConstraint (SubType (Primary loc) ty' codataType)
  return (Dtor () xt t' (fst <$> args'), retTypePos)
genConstraintsATerm (Match loc t cases) = do
  (t', matchType) <- genConstraintsATerm t
  (retTypePos, retTypeNeg) <- freshTVar Other
  cases' <- sequence (genConstraintsATermCase retTypeNeg <$> cases)
  addConstraint (SubType (Primary loc) matchType (TyData NegRep (snd <$> cases')))
  return (Match () t' (fst <$> cases'), retTypePos)
genConstraintsATerm (Comatch _ cocases) = do
  cocases' <- sequence (genConstraintsATermCocase <$> cocases)
  let ty = TyCodata PosRep (snd <$> cocases')
  return (Comatch () (fst <$> cocases'), ty)

genConstraintsATermCase :: Typ Neg -> ACase Loc FreeVarName -> GenM (ACase () FreeVarName, XtorSig Neg)
genConstraintsATermCase retType (MkACase { acase_ext, acase_name, acase_args, acase_term }) = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (\_ -> freshTVar Other)
  (acase_term', retTypeInf) <- local (\gr@GenerateReader{..} -> gr { context = (MkTypArgs argtsPos []):context }) (genConstraintsATerm acase_term)
  addConstraint (SubType (Primary acase_ext) retTypeInf retType)
  return (MkACase () acase_name acase_args acase_term', MkXtorSig acase_name (MkTypArgs argtsNeg []))

genConstraintsATermCocase :: ACase Loc FreeVarName -> GenM (ACase () FreeVarName, XtorSig Neg)
genConstraintsATermCocase (MkACase { acase_name, acase_args, acase_term }) = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (\_ -> freshTVar Other)
  (acase_term', retType) <- local (\gr@GenerateReader{..} -> gr { context = (MkTypArgs argtsPos []):context }) (genConstraintsATerm acase_term)
  let sig = MkXtorSig acase_name (MkTypArgs argtsNeg [retType])
  return (MkACase () acase_name acase_args acase_term', sig)

---------------------------------------------------------------------------------------------
-- Asymmetric Terms with recursive binding
---------------------------------------------------------------------------------------------

genConstraintsATermRecursive :: FreeVarName -> ATerm Loc FreeVarName -> GenM (ATerm () FreeVarName, Typ Pos)
genConstraintsATermRecursive fv tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  let modifyEnv (GenerateReader ctx env@Environment { defEnv }) = GenerateReader ctx env { defEnv = M.insert fv (FVar () fv, TypeScheme [] x) defEnv }
  (tm, ty) <- local modifyEnv (genConstraintsATerm tm)
  addConstraint (SubType Recursive ty y)
  return (tm, ty)
