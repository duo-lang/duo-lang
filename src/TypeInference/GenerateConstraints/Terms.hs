module TypeInference.GenerateConstraints.Terms
  ( genConstraintsTerm
  , genConstraintsTermRecursive
  , genConstraintsCommand
  ) where

import Control.Monad.Reader
import Data.Map qualified as M
import Data.Text qualified as T
import Pretty.Terms ()
import Pretty.Types ()
import Pretty.Constraints ()
import Pretty.Pretty ( ppPrint )
import Syntax.AST.Terms qualified as AST
import Syntax.RST.Terms qualified as RST
import Syntax.Common hiding (primOps)
import Syntax.RST.Types
import TypeInference.GenerateConstraints.Definition
import TypeInference.Constraints
import Utils
import Lookup
import TypeInference.GenerateConstraints.Primitives (primOps)
import Syntax.RST.Terms

---------------------------------------------------------------------------------------------
-- Substitutions and Linear Contexts
---------------------------------------------------------------------------------------------

genConstraintsPCTerm :: RST.PrdCnsTerm
                     -> GenM AST.PrdCnsTerm
genConstraintsPCTerm (RST.PrdTerm tm) = AST.PrdTerm <$> genConstraintsTerm tm
genConstraintsPCTerm (RST.CnsTerm tm) = AST.CnsTerm <$> genConstraintsTerm tm

genConstraintsSubst :: RST.Substitution
                    -> GenM AST.Substitution
genConstraintsSubst subst = sequence (genConstraintsPCTerm <$> subst)

genConstraintsCtxts :: LinearContext Pos -> LinearContext Neg -> ConstraintInfo -> GenM ()
genConstraintsCtxts ctx1 ctx2 info | length ctx1 /= length ctx2 = throwGenError ["genConstraintsCtxts: Linear contexts have unequal length"
                                                                                , "Constraint Info: " <> ppPrint info
                                                                                , "Pos context: " <> ppPrint ctx1
                                                                                , "Neg context: " <> ppPrint ctx2]
genConstraintsCtxts [] [] _ = return ()
genConstraintsCtxts ((PrdCnsType PrdRep ty1) : rest1) (PrdCnsType PrdRep ty2 : rest2) info = do
  addConstraint $ SubType info ty1 ty2
  genConstraintsCtxts rest1 rest2 info
genConstraintsCtxts ((PrdCnsType CnsRep ty1) : rest1) (PrdCnsType CnsRep ty2 : rest2) info = do
  addConstraint $ SubType info ty2 ty1
  genConstraintsCtxts rest1 rest2 info
genConstraintsCtxts (PrdCnsType PrdRep _:_) (PrdCnsType CnsRep _:_) info =
  throwGenError ["genConstraintsCtxts: Tried to constrain PrdType by CnsType", "Constraint Info: " <> ppPrint info]
genConstraintsCtxts (PrdCnsType CnsRep _:_) (PrdCnsType PrdRep _:_) info =
  throwGenError ["genConstraintsCtxts: Tried to constrain CnsType by PrdType", "ConstraintInfo: " <> ppPrint info]
genConstraintsCtxts [] (_:_) info =
  throwGenError ["genConstraintsCtxts: Linear contexts have unequal length.", "Constraint Info: " <> ppPrint info]
genConstraintsCtxts (_:_) [] info =
  throwGenError ["genConstraintsCtxts: Linear contexts have unequal length.", "Constraint Info: " <> ppPrint info]


splitContext :: Int -- ^ The offset of the projected type
             -> PrdCnsRep pc -- ^ The expected mode of the type
             -> LinearContext pol -- ^ The context to be split
             -> GenM (LinearContext pol, Typ (PrdCnsFlip pc pol), LinearContext pol)
splitContext n PrdRep sig = case splitAt n sig of
                              (_, []) -> throwGenError ["splitContext: Too short."]
                              (_, PrdCnsType CnsRep _:_) -> throwGenError ["splitContext: Found CnsType, expected PrdType."]
                              (tys1, PrdCnsType PrdRep ty:tys2) -> pure (tys1, ty, tys2)
splitContext n CnsRep sig = case splitAt n sig of
                              (_, []) -> throwGenError ["splitContext: Too short."]
                              (_, PrdCnsType PrdRep _:_) -> throwGenError ["splitContext: Found PrdType, expected CnsType."]
                              (tys1, PrdCnsType CnsRep ty:tys2) -> pure (tys1, ty, tys2)

---------------------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------------------

-- | Generate the constraints for a given Term.
genConstraintsTerm :: RST.Term pc
                    -> GenM (AST.Term pc)
--
-- Bound variables:
--
-- Bound variables can be looked up in the context.
--
genConstraintsTerm (RST.BoundVar loc rep idx) = do
  ty <- lookupContext rep idx
  return (AST.BoundVar loc rep ty idx)
--
-- Free variables:
--
-- Free variables can be looked up in the environment,
-- where they correspond to typing schemes. This typing
-- scheme has to be instantiated with fresh unification variables.
--
genConstraintsTerm (RST.FreeVar loc rep v) = do
  tys <- snd <$> lookupTerm rep v
  ty <- instantiateTypeScheme v loc tys
  return (AST.FreeVar loc rep ty v)
--
-- Structural Xtors:
--
genConstraintsTerm (RST.Xtor loc rep Structural xt subst) = do
  inferredSubst <- genConstraintsSubst subst
  let substTypes = AST.getTypArgs inferredSubst
  case rep of
    PrdRep -> return $ AST.Xtor loc rep (TyData   defaultLoc PosRep Nothing [MkXtorSig xt substTypes]) Structural xt inferredSubst
    CnsRep -> return $ AST.Xtor loc rep (TyCodata defaultLoc NegRep Nothing [MkXtorSig xt substTypes]) Structural xt inferredSubst
--
-- Nominal Xtors
--
genConstraintsTerm (RST.Xtor loc rep Nominal xt subst) = do
  -- First we infer the types of the arguments.
  substInferred <- genConstraintsSubst subst
  let substTypes = AST.getTypArgs substInferred
  -- Secondly we look up the argument types of the xtor in the type declaration.
  decl <- lookupDataDecl xt
  xtorSig <- lookupXtorSig xt NegRep
  -- Generate fresh unification variables for type parameters
  (args, tyParamsMap) <- freshTVarsForTypeParams (prdCnsToPol rep) decl
  -- Substitute these for the type parameters in the constructor signature
  let sig_args' = zonk tyParamsMap (sig_args xtorSig)
  -- Then we generate constraints between the inferred types of the substitution
  -- and the types we looked up, i.e. the types declared in the XtorSig.
  genConstraintsCtxts substTypes sig_args' (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
  case rep of
    PrdRep -> return (AST.Xtor loc rep (TyNominal defaultLoc PosRep Nothing (data_name decl) args) Nominal xt substInferred)
    CnsRep -> return (AST.Xtor loc rep (TyNominal defaultLoc NegRep Nothing (data_name decl) args) Nominal xt substInferred)
--
-- Refinement Xtors
--
genConstraintsTerm (RST.Xtor loc rep Refinement xt subst) = do
  -- First we infer the types of the arguments.
  substInferred <- genConstraintsSubst subst
  let substTypes = AST.getTypArgs substInferred
  -- Secondly we look up the argument types of the xtor in the type declaration.
  -- Since we infer refinement types, we have to look up the translated xtorSig.
  decl <- lookupDataDecl xt
  xtorSigUpper <- translateXtorSigUpper =<< lookupXtorSig xt NegRep
  -- Then we generate constraints between the inferred types of the substitution
  -- and the translations of the types we looked up, i.e. the types declared in the XtorSig.
  genConstraintsCtxts substTypes (sig_args xtorSigUpper) (case rep of { PrdRep -> CtorArgsConstraint loc; CnsRep -> DtorArgsConstraint loc })
  case rep of
    PrdRep -> return (AST.Xtor loc rep (TyData   defaultLoc PosRep (Just (data_name decl)) [MkXtorSig xt substTypes]) Refinement xt substInferred)
    CnsRep -> return (AST.Xtor loc rep (TyCodata defaultLoc NegRep (Just (data_name decl)) [MkXtorSig xt substTypes]) Refinement xt substInferred)
--
-- Structural pattern and copattern matches:
--
genConstraintsTerm (RST.XMatch loc rep Structural cases) = do
  inferredCases <- forM cases (\RST.MkCmdCase{cmdcase_args, cmdcase_name, cmdcase_ext, cmdcase_cmd} -> do
                      -- Generate positive and negative unification variables for all variables
                      -- bound in the pattern.
                      (uvarsPos, uvarsNeg) <- freshTVars cmdcase_args
                      -- Check the command in the context extended with the positive unification variables
                      cmdInferred <- withContext uvarsPos (genConstraintsCommand cmdcase_cmd)
                      -- Return the negative unification variables in the returned type.
                      return (AST.MkCmdCase cmdcase_ext cmdcase_name cmdcase_args cmdInferred, MkXtorSig cmdcase_name uvarsNeg))
  case rep of
    -- The return type is a structural type consisting of a XtorSig for each case.
    PrdRep -> return $ AST.XMatch loc rep (TyCodata defaultLoc PosRep Nothing (snd <$> inferredCases)) Structural (fst <$> inferredCases)
    CnsRep -> return $ AST.XMatch loc rep (TyData   defaultLoc NegRep Nothing (snd <$> inferredCases)) Structural (fst <$> inferredCases)
--
-- Nominal pattern and copattern matches
--
genConstraintsTerm (RST.XMatch _ _ Nominal []) =
  -- We know that empty matches cannot be parsed as nominal.
  -- It is therefore safe to pattern match on the head of the xtors in the other cases.
  throwGenError ["Unreachable: A nominal match needs to have at least one case."]
genConstraintsTerm (RST.XMatch loc rep Nominal cases@((DesugaredCmdCase _ _):_)) = 
  genConstraintsTerm (RST.XMatch loc rep Nominal (map (\(DesugaredCmdCase _ cs) -> cs) cases))
genConstraintsTerm (RST.XMatch loc rep Nominal cases@(pmcase:_)) = do
  -- We lookup the data declaration based on the first pattern match case.
  decl <- lookupDataDecl (RST.cmdcase_name pmcase)
  -- We check that all cases in the pattern match belong to the type declaration.
  checkCorrectness (RST.cmdcase_name <$> cases) decl
  -- We check that all xtors in the type declaration are matched against.
  checkExhaustiveness (RST.cmdcase_name <$> cases) decl
  -- Generate fresh unification variables for type parameters
  (args, tyParamsMap) <- freshTVarsForTypeParams (prdCnsToPol rep) decl

  inferredCases <- forM cases (\RST.MkCmdCase {..} -> do
                   -- We lookup the types belonging to the xtor in the type declaration.
                   posTypes <- sig_args <$> lookupXtorSig cmdcase_name PosRep
                   negTypes <- sig_args <$> lookupXtorSig cmdcase_name NegRep
                   -- Substitute fresh unification variables for type parameters
                   let posTypes' = zonk tyParamsMap posTypes
                   let negTypes' = zonk tyParamsMap negTypes
                   -- We generate constraints for the command in the context extended
                   -- with the types from the signature.
                   cmdInferred <- withContext posTypes' (genConstraintsCommand cmdcase_cmd)
                   return (AST.MkCmdCase cmdcase_ext cmdcase_name cmdcase_args cmdInferred, MkXtorSig cmdcase_name negTypes'))
  case rep of
    PrdRep -> return $ AST.XMatch loc rep (TyNominal defaultLoc PosRep Nothing (data_name decl) args) Nominal (fst <$> inferredCases)
    CnsRep -> return $ AST.XMatch loc rep (TyNominal defaultLoc NegRep Nothing (data_name decl) args) Nominal (fst <$> inferredCases)
--
-- Refinement pattern and copattern matches
--
genConstraintsTerm (RST.XMatch _ _ Refinement []) =
  -- We know that empty matches cannot be parsed as Refinement.
  -- It is therefore safe to pattern match on the head of the xtors in the other cases.
  throwGenError ["Unreachable: A refinement match needs to have at least one case."]
genConstraintsTerm (RST.XMatch loc rep Refinement cases@(pmcase:_)) = do
  -- We lookup the data declaration based on the first pattern match case.
  decl <- lookupDataDecl (RST.cmdcase_name pmcase)
  -- We check that all cases in the pattern match belong to the type declaration.
  checkCorrectness (RST.cmdcase_name <$> cases) decl
  inferredCases <- forM cases (\RST.MkCmdCase {..} -> do
                       -- Generate positive and negative unification variables for all variables
                       -- bound in the pattern.
                       (uvarsPos, uvarsNeg) <- freshTVars cmdcase_args
                       -- Check the command in the context extended with the positive unification variables
                       cmdInferred <- withContext uvarsPos (genConstraintsCommand cmdcase_cmd)
                       -- We have to bound the unification variables with the lower and upper bounds generated
                       -- from the information in the type declaration. These lower and upper bounds correspond
                       -- to the least and greatest type translation.
                       lowerBound <- sig_args <$> (translateXtorSigLower =<< lookupXtorSig cmdcase_name PosRep)
                       upperBound <- sig_args <$> (translateXtorSigUpper =<< lookupXtorSig cmdcase_name NegRep)
                       genConstraintsCtxts lowerBound uvarsNeg (PatternMatchConstraint loc)
                       genConstraintsCtxts uvarsPos upperBound (PatternMatchConstraint loc)
                       -- For the type, we return the unification variables which are now bounded by the least
                       -- and greatest type translation.
                       return (AST.MkCmdCase cmdcase_ext cmdcase_name cmdcase_args cmdInferred, MkXtorSig cmdcase_name uvarsNeg))
  case rep of
    PrdRep -> return $ AST.XMatch loc rep (TyCodata defaultLoc PosRep (Just (data_name decl)) (snd <$> inferredCases)) Refinement (fst <$> inferredCases)
    CnsRep -> return $ AST.XMatch loc rep (TyData   defaultLoc NegRep (Just (data_name decl)) (snd <$> inferredCases)) Refinement (fst <$> inferredCases)
--
-- Mu and TildeMu abstractions:
--
genConstraintsTerm (RST.MuAbs loc PrdRep bs cmd) = do
  (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
  cmdInferred <- withContext [PrdCnsType CnsRep uvneg] (genConstraintsCommand cmd)
  return (AST.MuAbs loc PrdRep uvpos bs cmdInferred)
genConstraintsTerm (RST.MuAbs loc CnsRep bs cmd) = do
  (uvpos, uvneg) <- freshTVar (ProgramVariable (fromMaybeVar bs))
  cmdInferred <- withContext [PrdCnsType PrdRep uvpos] (genConstraintsCommand cmd)
  return (AST.MuAbs loc CnsRep uvneg bs cmdInferred)
genConstraintsTerm (RST.PrimLitI64 loc i) = pure $ AST.PrimLitI64 loc i
genConstraintsTerm (RST.PrimLitF64 loc d) = pure $ AST.PrimLitF64 loc d
genConstraintsTerm (RST.Desugared t _) = genConstraintsTerm t

genConstraintsCommand :: RST.Command -> GenM AST.Command
genConstraintsCommand (RST.ExitSuccess loc) = return (AST.ExitSuccess loc)
genConstraintsCommand (RST.ExitFailure loc) = return (AST.ExitFailure loc)
genConstraintsCommand (RST.Jump loc fv) = do
  -- Ensure that the referenced command is in scope
  _ <- lookupCommand fv
  return (AST.Jump loc fv)
genConstraintsCommand (RST.Print loc prd cmd) = do
  prd' <- genConstraintsTerm prd
  cmd' <- genConstraintsCommand cmd
  return (AST.Print loc prd' cmd')
genConstraintsCommand (RST.Read loc cns) = do
  cns' <- genConstraintsTerm cns
  addConstraint (SubType (ReadConstraint loc)  (TyNominal defaultLoc PosRep Nothing peanoNm []) (AST.getTypeTerm cns'))
  return (AST.Read loc cns')
genConstraintsCommand (RST.Apply loc t1 t2) = do
  t1' <- genConstraintsTerm t1
  t2' <- genConstraintsTerm t2
  addConstraint (SubType (CommandConstraint loc) (AST.getTypeTerm t1') (AST.getTypeTerm t2'))
  return (AST.Apply loc Nothing t1' t2')
genConstraintsCommand (RST.PrimOp loc pt op subst) = do
  substInferred <- genConstraintsSubst subst
  let substTypes = AST.getTypArgs substInferred
  case M.lookup (pt, op) primOps of
    Nothing -> throwGenError [T.pack $ "Unreachable: Signature for primitive op " ++ primOpKeyword op ++ primTypeKeyword pt ++ " not defined"]
    Just sig -> do
      _ <- genConstraintsCtxts substTypes sig (PrimOpArgsConstraint loc)
      return (AST.PrimOp loc pt op substInferred)

---------------------------------------------------------------------------------------------
-- Checking recursive terms
---------------------------------------------------------------------------------------------

genConstraintsTermRecursive :: Loc
                            -> FreeVarName
                            -> PrdCnsRep pc -> RST.Term pc
                            -> GenM (AST.Term pc)
genConstraintsTermRecursive loc fv PrdRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  tm <- withTerm PrdRep fv (AST.FreeVar loc PrdRep x fv) loc (TypeScheme loc [] x) (genConstraintsTerm tm)
  addConstraint (SubType RecursionConstraint (AST.getTypeTerm tm) y)
  return tm
genConstraintsTermRecursive loc fv CnsRep tm = do
  (x,y) <- freshTVar (RecursiveUVar fv)
  tm <- withTerm CnsRep fv (AST.FreeVar loc CnsRep y fv) loc (TypeScheme loc [] y) (genConstraintsTerm tm)
  addConstraint (SubType RecursionConstraint x (AST.getTypeTerm tm))
  return tm
