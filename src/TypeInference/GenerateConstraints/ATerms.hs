module TypeInference.GenerateConstraints.ATerms
  ( genConstraintsATerm
  , genConstraintsATermRecursive
  ) where

import Control.Monad (forM)

import Syntax.ATerms
import Syntax.Types
import TypeInference.GenerateConstraints.Definition
import Utils
import Data.List
import Data.Maybe

---------------------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------------------

-- | Every asymmetric terms gets assigned a positive type.
genConstraintsATerm :: ATerm Loc FreeVarName
                    -> GenM ( ATerm () FreeVarName
                            , Typ Pos)
genConstraintsATerm (BVar _ idx) = do
  ty <- lookupContext PrdRep idx
  return (BVar () idx, ty)
genConstraintsATerm (FVar loc fv) = do
  tys <- lookupDefEnv fv
  ty <- instantiateTypeScheme fv loc tys
  return (FVar () fv, ty)

genConstraintsATerm (Ctor _ xt@MkXtorName { xtorNominalStructural = Structural } args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  let ty = TyData PosRep [MkXtorSig xt (MkTypArgs (snd <$> args') [])]
  return (Ctor () xt (fst <$> args'), ty)
genConstraintsATerm (Ctor _ xt@MkXtorName { xtorNominalStructural = Nominal } args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  tn <- lookupDataDecl xt -- TODO: check args
  return (Ctor () xt (fst <$> args'), TyNominal PosRep (data_name tn) )

genConstraintsATerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Structural } t args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  (retTypePos, retTypeNeg) <- freshTVar (DtorAp loc)
  let codataType = TyCodata NegRep [MkXtorSig xt (MkTypArgs (snd <$> args') [retTypeNeg])]
  (t', ty') <- genConstraintsATerm t
  addConstraint (SubType (DtorApConstraint loc) ty' codataType)
  return (Dtor () xt t' (fst <$> args'), retTypePos)
genConstraintsATerm (Dtor loc xt@MkXtorName { xtorNominalStructural = Nominal } t args) = do
  args' <- sequence (genConstraintsATerm <$> args)
  tn <- lookupDataDecl xt
  (t', ty') <- genConstraintsATerm t
  addConstraint (SubType (DtorApConstraint loc) ty' (TyNominal NegRep (data_name tn)) )
  let xtorSig = fromJust $ find ( \xs -> sig_name xs == xt ) (data_xtors tn)
  let name = case head $ cnsTypes $ sig_args xtorSig of { TyNominal _ tn -> tn; _ -> undefined}
  return (Dtor () xt t' (fst <$> args'), TyNominal PosRep name)

genConstraintsATerm (Match loc t cases) = do
  (t', matchType) <- genConstraintsATerm t
  (retTypePos, retTypeNeg) <- freshTVar (PatternMatch loc)
  cases' <- sequence (genConstraintsATermCase retTypeNeg <$> cases)
  addConstraint (SubType (PatternMatchConstraint loc) matchType (TyData NegRep (snd <$> cases')))
  return (Match () t' (fst <$> cases'), retTypePos)

genConstraintsATerm (Comatch _ cocases) = do
  cocases' <- sequence (genConstraintsATermCocase <$> cocases)
  let ty = TyCodata PosRep (snd <$> cocases')
  return (Comatch () (fst <$> cocases'), ty)

genConstraintsATermCase :: Typ Neg
                        -> ACase Loc FreeVarName
                        -> GenM (ACase () FreeVarName, XtorSig Neg)
genConstraintsATermCase retType (MkACase { acase_ext, acase_name, acase_args, acase_term }) = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (\fv -> freshTVar (ProgramVariable fv))
  (acase_term', retTypeInf) <- withContext (MkTypArgs argtsPos []) (genConstraintsATerm acase_term)
  addConstraint (SubType (CaseConstraint acase_ext) retTypeInf retType) -- Case type
  return (MkACase () acase_name acase_args acase_term', MkXtorSig acase_name (MkTypArgs argtsNeg []))

genConstraintsATermCocase :: ACase Loc FreeVarName
                          -> GenM (ACase () FreeVarName, XtorSig Neg)
genConstraintsATermCocase (MkACase { acase_name, acase_args, acase_term }) = do
  (argtsPos,argtsNeg) <- unzip <$> forM acase_args (\fv -> freshTVar (ProgramVariable fv))
  (acase_term', retType) <- withContext (MkTypArgs argtsPos []) (genConstraintsATerm acase_term)
  let sig = MkXtorSig acase_name (MkTypArgs argtsNeg [retType])
  return (MkACase () acase_name acase_args acase_term', sig)
 
---------------------------------------------------------------------------------------------
-- Asymmetric Terms with recursive binding
---------------------------------------------------------------------------------------------

genConstraintsATermRecursive :: FreeVarName
                             -> ATerm Loc FreeVarName
                             -> GenM (ATerm () FreeVarName, Typ Pos)
genConstraintsATermRecursive fv tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  (tm, ty) <- withDefEnv fv (FVar () fv) (TypeScheme [] x) (genConstraintsATerm tm)
  addConstraint (SubType RecursionConstraint ty y)
  return (tm, ty)
