{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant multi-way if" #-}
module Resolution.Terms (resolveTerm, resolveCommand, resolveInstanceCases) where

import Control.Monad (when, forM)
import Control.Monad.Except (throwError)
import Data.Bifunctor ( second )
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Text qualified as T

import Errors
import Pretty.Pretty ( ppPrint )
import Resolution.Definition
import Resolution.SymbolTable
import Resolution.Pattern
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCns(..), Arity, PrdCnsRep(..))
import Syntax.CST.Names
import Utils

---------------------------------------------------------------------------------
-- Check Arity of Xtor
---------------------------------------------------------------------------------

-- can only be called when length ar == length tms
resolveTerms :: Loc -> Arity -> [CST.Term] -> ResolverM [RST.PrdCnsTerm]
resolveTerms _ [] [] = return []
resolveTerms loc (Prd:ar) (t:tms) = do
  t' <- RST.PrdTerm <$> resolveTerm PrdRep t
  tms' <- resolveTerms loc ar tms
  pure $ t' : tms'
resolveTerms loc (Cns:ar) (t:tms) = do
  t' <- RST.CnsTerm <$> resolveTerm CnsRep t
  tms' <- resolveTerms loc ar tms
  pure $ t' : tms'
resolveTerms loc ar t = error $ "compiler bug in resolveTerms, loc = " ++ show loc ++ ", ar = " ++ show ar ++ ", t = " ++ show t

---------------------------------------------------------------------------------
-- Analyze Cases
---------------------------------------------------------------------------------

-- | A case with no stars.
data IntermediateCase  = MkIntermediateCase
  { icase_loc  :: Loc
  , icase_name :: XtorName
  , icase_args :: [(PrdCns, FreeVarName)]
  , icase_term :: CST.Term
  }

-- | A case with exactly one star.
data IntermediateCaseI pc = MkIntermediateCaseI
  { icasei_loc  :: Loc
  , icasei_name :: XtorName
  , icasei_args :: ([(PrdCns, FreeVarName)], PrdCnsRep pc,[(PrdCns,FreeVarName)])
  , icasei_term :: CST.Term
  }

data SomeIntermediateCase where
  ExplicitCase ::                 IntermediateCase     -> SomeIntermediateCase
  ImplicitCase :: PrdCnsRep pc -> IntermediateCaseI pc -> SomeIntermediateCase

isExplicitCase :: SomeIntermediateCase -> Bool
isExplicitCase (ExplicitCase _) = True
isExplicitCase _                = False

isImplicitCase :: PrdCnsRep pc -> SomeIntermediateCase -> Bool
isImplicitCase PrdRep (ImplicitCase PrdRep _) = True
isImplicitCase CnsRep (ImplicitCase CnsRep _) = True
isImplicitCase _      _                       = False

fromExplicitCase :: SomeIntermediateCase -> IntermediateCase
fromExplicitCase (ExplicitCase cs) = cs
fromExplicitCase _                 = error "Compiler bug"

fromImplicitCase :: PrdCnsRep pc -> SomeIntermediateCase -> IntermediateCaseI pc
fromImplicitCase PrdRep (ImplicitCase PrdRep cs) = cs
fromImplicitCase CnsRep (ImplicitCase CnsRep cs) = cs
fromImplicitCase _      _                        = error "Compiler bug"

data SomeIntermediateCases where
  ExplicitCases    ::                 [IntermediateCase]     -> SomeIntermediateCases
  ImplicitCases    :: PrdCnsRep pc -> [IntermediateCaseI pc] -> SomeIntermediateCases

adjustPat :: (Loc, PrdCns, FreeVarName) -> (PrdCns, FreeVarName)
adjustPat (_loc, pc, var) = (pc,var)

-- Refines `CST.TermCase` to either `IntermediateCase` or `IntermediateCaseI`, depending on
-- the number of stars.
analyzeCase :: CST.DataCodata
            -- ^ Whether a constructor (Data) or destructor (Codata) is expected in this case
            -> CST.TermCase
            -> ResolverM SomeIntermediateCase
analyzeCase dc CST.MkTermCase { tmcase_loc, tmcase_pat, tmcase_term } = do
  analyzedPattern <- analyzePattern dc tmcase_pat
  case analyzedPattern of
    ExplicitPattern _ xt pat -> pure $ ExplicitCase $ MkIntermediateCase
                                    { icase_loc = tmcase_loc
                                    , icase_name = xt
                                    , icase_args = adjustPat <$> pat
                                    , icase_term = tmcase_term
                                    }
    ImplicitPrdPattern _ xt pat -> pure $ ImplicitCase PrdRep $ MkIntermediateCaseI
                                    { icasei_loc = tmcase_loc
                                    , icasei_name = xt
                                    , icasei_args = case pat of (pat1,pc,pat2) -> (adjustPat <$> pat1, pc, adjustPat <$> pat2)
                                    , icasei_term = tmcase_term
                                    }
    ImplicitCnsPattern _ xt pat -> pure $ ImplicitCase CnsRep $ MkIntermediateCaseI
                                    { icasei_loc = tmcase_loc
                                    , icasei_name = xt
                                    , icasei_args = case pat of (pat1,pc,pat2) -> (adjustPat <$> pat1, pc, adjustPat <$> pat2)
                                    , icasei_term = tmcase_term
                                    }

analyzeCases :: CST.DataCodata
             -> [CST.TermCase]
             -> ResolverM SomeIntermediateCases
analyzeCases dc cases = do
  cases' <- sequence $ analyzeCase dc <$> cases
  if | all isExplicitCase cases' -> pure $ ExplicitCases    $ fromExplicitCase <$> cases'
     | all (isImplicitCase PrdRep) cases' -> pure $ ImplicitCases PrdRep $ fromImplicitCase PrdRep <$> cases'
     | all (isImplicitCase CnsRep) cases' -> pure $ ImplicitCases CnsRep $ fromImplicitCase CnsRep <$> cases'
     | otherwise -> throwOtherError (getLoc (head cases)) ["Cases mix the use of both explicit and implicit patterns."]

analyzeInstanceCase :: CST.TermCase -> ResolverM SomeIntermediateCase
analyzeInstanceCase CST.MkTermCase { tmcase_loc, tmcase_pat, tmcase_term } = do
  analyzedPattern <- analyzeInstancePattern tmcase_pat
  case analyzedPattern of
    ExplicitPattern _ xt pat -> pure $ ExplicitCase $ MkIntermediateCase
                                    { icase_loc = tmcase_loc
                                    , icase_name = xt
                                    , icase_args = adjustPat <$> pat
                                    , icase_term = tmcase_term
                                    }
    _ -> throwOtherError defaultLoc ["Should be unreachable"]

---------------------------------------------------------------------------------
-- Resolve Cases
---------------------------------------------------------------------------------

resolveCommandCase :: IntermediateCase -> ResolverM RST.CmdCase
resolveCommandCase MkIntermediateCase { icase_loc , icase_name , icase_args , icase_term } = do
  cmd' <- resolveCommand icase_term
  pure RST.MkCmdCase { cmdcase_loc = icase_loc
                     , cmdcase_pat = RST.XtorPat icase_loc icase_name (second Just <$> icase_args)
                     , cmdcase_cmd = RST.commandClosing icase_args cmd'
                     }

resolveTermCaseI :: PrdCnsRep pc -> IntermediateCaseI pc -> ResolverM (RST.TermCaseI pc)
resolveTermCaseI rep MkIntermediateCaseI { icasei_loc, icasei_name, icasei_args = (args1,_, args2), icasei_term } = do
  tm' <- resolveTerm rep icasei_term
  pure RST.MkTermCaseI { tmcasei_loc = icasei_loc
                       , tmcasei_pat = RST.XtorPatI icasei_loc icasei_name (second Just <$> args1, (), second Just <$> args2)
                       , tmcasei_term = RST.termClosing (args1 ++ [(Cns, MkFreeVarName "*")] ++ args2) tm'
                       }

resolveTermCase :: PrdCnsRep pc -> IntermediateCase -> ResolverM (RST.TermCase pc)
resolveTermCase rep MkIntermediateCase { icase_loc, icase_name, icase_args, icase_term } = do
  tm' <- resolveTerm rep icase_term
  pure RST.MkTermCase { tmcase_loc  = icase_loc
                      , tmcase_pat = RST.XtorPat icase_loc icase_name (second Just <$> icase_args)
                      , tmcase_term = RST.termClosing icase_args tm'
                      }

resolveInstanceCase :: IntermediateCase -> ResolverM RST.InstanceCase
resolveInstanceCase MkIntermediateCase { icase_loc , icase_name , icase_args , icase_term } = do
  cmd' <- resolveCommand icase_term
  pure RST.MkInstanceCase { instancecase_loc = icase_loc
                          , instancecase_pat = RST.XtorPat icase_loc icase_name (second Just <$> icase_args)
                          , instancecase_cmd = RST.commandClosing icase_args cmd'
                          }


resolveInstanceCases :: [CST.TermCase] -> ResolverM [RST.InstanceCase]
resolveInstanceCases cases = do
  intermediateCases <- sequence $ analyzeInstanceCase <$> cases
  sequence $ resolveInstanceCase . fromExplicitCase <$> intermediateCases


---------------------------------------------------------------------------------
-- Resolving PrimCommands
---------------------------------------------------------------------------------

resolvePrimCommand :: Loc -> PrimName -> [CST.Term] -> ResolverM RST.Command
-- 0 arguments
resolvePrimCommand loc nm [] =
  if | nm == exitSuccessName -> pure $ RST.ExitSuccess loc
     | nm == exitFailureName -> pure $ RST.ExitFailure loc
     | otherwise             -> throwError $ ErrResolution (PrimOpArityMismatch loc nm 0) :| []
-- 1 argument
resolvePrimCommand loc nm [tm] | nm == readName =
  if | nm == readName -> do
               tm' <- resolveTerm CnsRep tm
               pure $ RST.Read loc tm'
     | otherwise      -> throwError $ ErrResolution (PrimOpArityMismatch loc nm 1) :| []
-- 2 arguments
resolvePrimCommand loc nm [tm, cmd] | nm == printName = do
  tm' <- resolveTerm PrdRep tm
  cmd' <- resolveCommand cmd
  pure $ RST.Print loc tm' cmd'
--3 arguments
resolvePrimCommand loc nm [tm1,tm2,tm3] = do
  tm1' <- resolveTerm PrdRep tm1
  tm2' <- resolveTerm PrdRep tm2
  tm3' <- resolveTerm CnsRep tm3
  let args = [RST.PrdTerm tm1', RST.PrdTerm tm2', RST.CnsTerm tm3']
  if | nm == MkPrimName "#I64Add" -> pure (RST.PrimOp loc RST.I64Add args)
     | nm == MkPrimName "#I64Sub" -> pure (RST.PrimOp loc RST.I64Sub args)
     | nm == MkPrimName "#I64Mul" -> pure (RST.PrimOp loc RST.I64Mul args)
     | nm == MkPrimName "#I64Div" -> pure (RST.PrimOp loc RST.I64Div args)
     | nm == MkPrimName "#I64Mod" -> pure (RST.PrimOp loc RST.I64Mod args)
     | nm == MkPrimName "#F64Add" -> pure (RST.PrimOp loc RST.F64Add args)
     | nm == MkPrimName "#F64Sub" -> pure (RST.PrimOp loc RST.F64Sub args)
     | nm == MkPrimName "#F64Mul" -> pure (RST.PrimOp loc RST.F64Mul args)
     | nm == MkPrimName "#F64Div" -> pure (RST.PrimOp loc RST.F64Div args)
     | nm == MkPrimName "#CharPrepend" -> pure (RST.PrimOp loc RST.CharPrepend args)
     | nm == MkPrimName "#StringAppend" -> pure (RST.PrimOp loc RST.StringAppend args)
     | otherwise -> throwError $ ErrResolution (PrimOpArityMismatch loc nm 3) :| []
-- More arguments
resolvePrimCommand loc nm args = throwError $ ErrResolution (PrimOpArityMismatch loc nm (length args)) :| []

---------------------------------------------------------------------------------
-- Resolving Commands
---------------------------------------------------------------------------------

resolveCommand :: CST.Term -> ResolverM RST.Command
resolveCommand (CST.TermParens _loc cmd) =
  resolveCommand cmd
resolveCommand (CST.Var loc fv) =
  pure $ RST.Jump loc fv
resolveCommand (CST.PrimTerm loc nm args) =
  resolvePrimCommand loc nm args
resolveCommand (CST.Apply loc tm1 tm2) = do
  tm1' <- resolveTerm PrdRep tm1
  tm2' <- resolveTerm CnsRep tm2
  pure $ RST.Apply loc tm1' tm2'
---------------------------------------------------------------------------------
-- CaseOf / CocaseOf
---------------------------------------------------------------------------------
resolveCommand (CST.CaseOf loc tm cases) = do
  tm' <- resolveTerm PrdRep tm
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cmdCases <- sequence $ resolveCommandCase <$> explicitCases
      pure $ RST.CaseOfCmd loc ns tm' cmdCases
    ImplicitCases rep implicitCases -> do
      termCasesI <- sequence $ resolveTermCaseI rep <$> implicitCases
      pure $ RST.CaseOfI loc rep ns tm' termCasesI
resolveCommand (CST.CocaseOf loc tm cases) = do
  tm' <- resolveTerm CnsRep tm
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cmdCases <- sequence $ resolveCommandCase <$> explicitCases
      pure $ RST.CocaseOfCmd loc ns tm' cmdCases
    ImplicitCases rep implicitCases -> do
      termCasesI <- sequence $ resolveTermCaseI rep <$> implicitCases
      pure $ RST.CocaseOfI loc rep ns tm' termCasesI
resolveCommand (CST.Xtor loc xtor arity) = do
  (_, res) <- lookupXtor loc xtor
  case res of
    (XtorNameResult _dc _ns _ar) -> throwError $ ErrResolution (CmdExpected loc "Method (Command) expected, but found Xtor") :| []
    (MethodNameResult cn ar) -> do
      let mn = MkMethodName $ unXtorName xtor
      analyzedSubst <- analyzeMethodSubstitution loc mn cn ar arity
      subst' <- case analyzedSubst of
          ExplicitSubst es -> return (map snd es)
          ImplicitSubst {} ->  throwOtherError loc ["The substitution in a method call cannot contain implicit arguments"]
      pctms <- resolveTerms loc ar subst'
      pure $! RST.Method loc mn cn pctms
---------------------------------------------------------------------------------
-- CST constructs which can only be resolved to commands
---------------------------------------------------------------------------------
resolveCommand (CST.Semi loc _ _ _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found Semi") :| []
resolveCommand (CST.Dtor loc _ _ _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found Dtor") :| []
resolveCommand (CST.Case loc _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found Case") :| []
resolveCommand (CST.Cocase loc _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found Cocase") :| []
resolveCommand (CST.MuAbs loc _ _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found Mu abstraction") :| []
resolveCommand (CST.PrimLitI64 loc _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found #I64 literal") :| []
resolveCommand (CST.PrimLitF64 loc _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found #F64 literal") :| []
resolveCommand (CST.PrimLitChar loc _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found #Char literal") :| []
resolveCommand (CST.PrimLitString loc _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found #String literal") :| []
resolveCommand (CST.NatLit loc _ _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found Nat literal") :| []
resolveCommand (CST.FunApp loc _ _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found function application") :| []
resolveCommand (CST.Lambda loc _ _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found lambda abstraction") :| []
resolveCommand (CST.CoLambda loc _ _) =
  throwError $ ErrResolution (CmdExpected loc "Command expected, but found cofunction abstraction") :| []



casesToNS :: [CST.TermCase] -> ResolverM CST.NominalStructural
casesToNS [] = pure CST.Structural
casesToNS (CST.MkTermCase { tmcase_loc, tmcase_pat = CST.PatXtor _ tmcase_name _ }:_) = do
  (_, XtorNameResult _ ns _) <- lookupXtor tmcase_loc tmcase_name
  pure ns
casesToNS _ =
  throwOtherError defaultLoc ["casesToNS called with invalid argument"]

-- | Lower a natural number literal.
resolveNatLit :: Loc -> CST.NominalStructural -> Int -> ResolverM (RST.Term Prd)
resolveNatLit loc ns 0 = pure $ RST.Xtor loc PrdRep ns (MkXtorName "Z") []
resolveNatLit loc ns n = do
  n' <- resolveNatLit loc ns (n-1)
  pure $ RST.Xtor loc PrdRep ns (MkXtorName "S") [RST.PrdTerm n']

-- | Lower an application.
resolveApp :: PrdCnsRep pc -> Loc -> CST.Term -> CST.Term -> ResolverM (RST.Term pc)
resolveApp PrdRep loc fun arg = do
  fun' <- resolveTerm PrdRep fun
  arg' <- resolveTerm PrdRep arg
  pure $ RST.Dtor loc PrdRep CST.Nominal (MkXtorName "Ap") fun' ([RST.PrdTerm arg'],PrdRep,[])
resolveApp CnsRep loc fun arg = do
  fun' <- resolveTerm CnsRep fun
  arg' <- resolveTerm CnsRep arg
  pure $ RST.Semi loc CnsRep CST.Nominal (MkXtorName "CoAp")  ([RST.CnsTerm arg'],CnsRep,[]) fun'

isStarT :: CST.TermOrStar -> Bool
isStarT CST.ToSStar  = True
isStarT _ = False

toTm  :: CST.TermOrStar -> CST.Term
toTm (CST.ToSTerm t) = t
toTm _x = error "Compiler bug: toFV"

---------------------------------------------------------------------------------
-- Analyze a substitution which (may) contain a star
---------------------------------------------------------------------------------
data AnalyzedSubstitution where
  ExplicitSubst :: [(PrdCns, CST.Term)] -> AnalyzedSubstitution
  ImplicitSubst :: [(PrdCns, CST.Term)] -> PrdCns -> [(PrdCns, CST.Term)] -> AnalyzedSubstitution

analyzeSubstitution :: Loc -> Arity -> [CST.TermOrStar] -> ResolverM AnalyzedSubstitution
analyzeSubstitution loc arity subst = do
  -- Dispatch on the number of stars in the substitution
  case length (filter isStarT subst) of
    0 -> pure $ ExplicitSubst (zip arity (toTm <$> subst))
    1 -> do
      let zipped :: [(PrdCns, CST.TermOrStar)] = zip arity subst
      case span (not . isStarT . snd) zipped of
        (subst1,(pc,_):subst2) -> pure $ ImplicitSubst (second toTm <$> subst1) pc (second toTm <$> subst2)
        _ -> throwOtherError loc ["Compiler bug in analyzeSubstitution"]
    n -> throwOtherError loc ["At most one star expected. Got " <> T.pack (show n) <> " stars."]

analyzeXtorSubstitution :: Loc -> XtorName -> Arity -> [CST.TermOrStar] -> ResolverM AnalyzedSubstitution
analyzeXtorSubstitution loc xtor arity subst = do
  -- Check whether the arity corresponds to the length of the substitution
  when (length arity /= length subst) $
    throwError $ ErrResolution (XtorArityMismatch loc xtor (length arity) (length subst)) :| []
  analyzeSubstitution loc arity subst

analyzeMethodSubstitution :: Loc -> MethodName -> ClassName -> Arity -> [CST.TermOrStar] -> ResolverM AnalyzedSubstitution
analyzeMethodSubstitution loc mn cn arity subst = do
  -- Check whether the arity corresponds to the length of the substitution
  when (length arity /= length subst) $
    throwError $ ErrResolution (MethodArityMismatch loc mn cn (length arity) (length subst)) :| []
  analyzeSubstitution loc arity subst

resolvePrdCnsTerm :: PrdCns -> CST.Term -> ResolverM RST.PrdCnsTerm
resolvePrdCnsTerm Prd tm = RST.PrdTerm <$> resolveTerm PrdRep tm
resolvePrdCnsTerm Cns tm = RST.CnsTerm <$> resolveTerm CnsRep tm

resolveTerm :: PrdCnsRep pc -> CST.Term -> ResolverM (RST.Term pc)
resolveTerm rep (CST.TermParens _loc tm) =
  resolveTerm rep tm
resolveTerm rep (CST.Var loc v) =
  pure $ RST.FreeVar loc rep v
---------------------------------------------------------------------------------
-- Mu abstraction
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.MuAbs loc fv cmd) = do
  cmd' <- resolveCommand cmd
  pure $ RST.MuAbs loc PrdRep (Just fv) (RST.commandClosing [(Cns,fv)] cmd')
resolveTerm CnsRep (CST.MuAbs loc fv cmd) = do
  cmd' <- resolveCommand cmd
  pure $ RST.MuAbs loc CnsRep (Just fv) (RST.commandClosing [(Prd,fv)] cmd')
---------------------------------------------------------------------------------
-- Xtor
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.Xtor loc xtor subst) = do
  (_, res) <- lookupXtor loc xtor
  case res of
    (XtorNameResult dc ns ar) -> do
      when (length ar /= length subst) $
               throwError $ ErrResolution (XtorArityMismatch loc xtor (length ar) (length subst)) :| []
      when (dc /= CST.Data) $
               throwOtherError loc ["The given xtor " <> ppPrint xtor <> " is declared as a destructor, not a constructor."]
      analyzedSubst <- analyzeXtorSubstitution loc xtor ar subst
      subst' <- case analyzedSubst of
          ExplicitSubst es -> return (map snd es)
          ImplicitSubst {} ->  throwOtherError loc ["The substitution in a constructor call cannot contain implicit arguments"]
      pctms <- resolveTerms loc ar subst'
      pure $ RST.Xtor loc PrdRep ns xtor pctms
    (MethodNameResult _cn _ar) -> throwOtherError loc ["Xtor expected, but found Method"]
resolveTerm CnsRep (CST.Xtor loc xtor subst) = do
  (_, res) <- lookupXtor loc xtor
  case res of
    (XtorNameResult dc ns ar) -> do
      when (length ar /= length subst) $
               throwError $ ErrResolution (XtorArityMismatch loc xtor (length ar) (length subst)) :| []
      when (dc /= CST.Codata) $
               throwOtherError loc ["The given xtor " <> ppPrint xtor <> " is declared as a constructor, not a destructor."]
      analyzedSubst <- analyzeXtorSubstitution loc xtor ar subst
      subst' <- case analyzedSubst of
          ExplicitSubst es -> return (map snd es)
          ImplicitSubst {} ->  throwOtherError loc ["The substitution in a constructor call cannot contain implicit arguments"]
      pctms <- resolveTerms loc ar subst'
      pure $ RST.Xtor loc CnsRep ns xtor pctms
    (MethodNameResult _cn _ar) -> throwOtherError loc ["Xtor expected, but found Method"]
---------------------------------------------------------------------------------
-- Semi / Dtor
---------------------------------------------------------------------------------
resolveTerm rep (CST.Semi loc xtor subst tm) = do
  tm' <- resolveTerm CnsRep tm
  (_, XtorNameResult dc ns ar) <- lookupXtor loc xtor
  when (dc /= CST.Data) $
           throwOtherError loc ["The given xtor " <> ppPrint xtor <> " is declared as a destructor, not a constructor."]
  analyzedSubst <- analyzeXtorSubstitution loc xtor ar subst
  case analyzedSubst of
    ExplicitSubst _explicitSubst -> do
      throwOtherError loc ["The substitution in a Semi must contain at least one implicit argument"]
    ImplicitSubst subst1 Prd subst2 -> do
      case rep of
        PrdRep ->
          throwOtherError loc ["Tried to resolve Semi to a producer, but implicit argument stands for a producer"]
        CnsRep -> do
          subst1' <- forM subst1 $ uncurry resolvePrdCnsTerm
          subst2' <- forM subst2 $ uncurry resolvePrdCnsTerm
          pure $ RST.Semi loc CnsRep ns xtor (subst1', CnsRep, subst2') tm'
    ImplicitSubst subst1 Cns subst2 -> do
      case rep of
        PrdRep -> do
          subst1' <- forM subst1 $ uncurry resolvePrdCnsTerm
          subst2' <- forM subst2 $ uncurry resolvePrdCnsTerm
          pure $ RST.Semi loc PrdRep ns xtor (subst1', PrdRep, subst2') tm'
        CnsRep ->
          throwOtherError loc ["Tried to resolve Semi to a producer, but implicit argument stands for a producer"]
resolveTerm rep (CST.Dtor loc xtor tm subst) = do
  tm' <- resolveTerm PrdRep tm
  (_, XtorNameResult dc ns ar) <- lookupXtor loc xtor
  when (dc /= CST.Codata) $
           throwOtherError loc ["The given xtor " <> ppPrint xtor <> " is declared as a constructor, not a destructor."]
  analyzedSubst <- analyzeXtorSubstitution loc xtor ar subst
  case analyzedSubst of
    ExplicitSubst _explicitSubst -> do
      throwOtherError loc ["The substitution in a dtor must contain at least one implicit argument"]
    ImplicitSubst subst1 Prd subst2 -> do
      case rep of
        PrdRep -> do
          throwOtherError loc ["Tried to resolve Dtor to a producer, but implicit argument stands for a producer"]
        CnsRep -> do
          subst1' <- forM subst1 $ uncurry resolvePrdCnsTerm
          subst2' <- forM subst2 $ uncurry resolvePrdCnsTerm
          pure $ RST.Dtor loc CnsRep ns xtor tm' (subst1', CnsRep, subst2')
    ImplicitSubst subst1 Cns subst2 -> do
      case rep of
        PrdRep -> do
          subst1' <- forM subst1 $ uncurry resolvePrdCnsTerm
          subst2' <- forM subst2 $ uncurry resolvePrdCnsTerm
          pure $ RST.Dtor loc PrdRep ns xtor tm' (subst1', PrdRep, subst2')
        CnsRep -> do
          throwOtherError loc ["Tried to resolve Dtor to a consumer, but implicit argument stands for consumer"]
---------------------------------------------------------------------------------
-- Case / Cocase
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.Case loc _) =
  throwOtherError loc ["Cannot resolve pattern match to a producer."]
resolveTerm CnsRep (CST.Cocase loc _) =
  throwOtherError loc ["Cannot resolve copattern match to a consumer."]
resolveTerm PrdRep (CST.Cocase loc cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence $ resolveCommandCase <$> explicitCases
      pure $ RST.XCase loc PrdRep ns cases'
    ImplicitCases rep implicitCases -> do
      cases' <- sequence $ resolveTermCaseI rep <$> implicitCases
      pure $ RST.CocaseI loc rep ns cases'
resolveTerm CnsRep (CST.Case loc cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence $ resolveCommandCase <$> explicitCases
      pure $ RST.XCase loc CnsRep ns cases'
    ImplicitCases rep implicitCases -> do
      cases' <- sequence $ resolveTermCaseI rep <$> implicitCases
      pure $ RST.CaseI loc rep ns cases'
---------------------------------------------------------------------------------
-- CaseOf / CocaseOf
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.CaseOf loc t cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (resolveTermCase PrdRep <$> explicitCases)
      t' <- resolveTerm PrdRep t
      pure $ RST.CaseOf loc PrdRep ns t' cases'
    ImplicitCases _rep _implicitCases ->
      throwOtherError loc ["Cannot resolve case-of with implicit cases to producer."]
resolveTerm PrdRep (CST.CocaseOf loc t cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (resolveTermCase PrdRep <$> explicitCases)
      t' <- resolveTerm CnsRep t
      pure $ RST.CocaseOf loc PrdRep ns t' cases'
    ImplicitCases _rep _implicitCases ->
      throwOtherError loc ["Cannot resolve cocase-of with implicit cases to producer"]
resolveTerm CnsRep (CST.CaseOf loc t cases) = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (resolveTermCase CnsRep <$> explicitCases)
      t' <- resolveTerm PrdRep t
      pure $ RST.CaseOf loc CnsRep ns t' cases'
    ImplicitCases _rep _implicitCases ->
      throwOtherError loc ["Cannot resolve case-of with implicit cases to consumer."]
resolveTerm CnsRep (CST.CocaseOf loc t cases) = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (resolveTermCase CnsRep <$> explicitCases)
      t' <- resolveTerm CnsRep t
      pure $ RST.CocaseOf loc CnsRep ns t' cases'
    ImplicitCases _rep _implicitCases ->
      throwOtherError loc ["Cannot resolve cocase-of with implicit cases to consumer"]
---------------------------------------------------------------------------------
-- Literals
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.PrimLitI64 loc i) =
  pure $ RST.PrimLitI64 loc i
resolveTerm CnsRep (CST.PrimLitI64 loc _) =
  throwOtherError loc ["Cannot resolve primitive literal to a consumer."]
resolveTerm PrdRep (CST.PrimLitF64 loc d) =
  pure $ RST.PrimLitF64 loc d
resolveTerm CnsRep (CST.PrimLitF64 loc _) =
  throwOtherError loc ["Cannot resolve primitive literal to a consumer."]
resolveTerm PrdRep (CST.PrimLitChar loc d) =
  pure $ RST.PrimLitChar loc d
resolveTerm CnsRep (CST.PrimLitChar loc _) =
  throwOtherError loc ["Cannot resolve primitive literal to a consumer."]
resolveTerm PrdRep (CST.PrimLitString loc d) =
  pure $ RST.PrimLitString loc d
resolveTerm CnsRep (CST.PrimLitString loc _) =
  throwOtherError loc ["Cannot resolve primitive literal to a consumer."]
resolveTerm PrdRep (CST.NatLit loc ns i) =
  resolveNatLit loc ns i
resolveTerm CnsRep (CST.NatLit loc _ns _i) =
  throwOtherError loc ["Cannot resolve NatLit to a consumer."]
---------------------------------------------------------------------------------
-- Function specific syntax sugar
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.Lambda loc fv tm) =
  do
    tm' <- resolveTerm PrdRep tm
    let tm'' = RST.termClosing [(Prd,fv)] tm'
    return $ RST.Lambda loc PrdRep fv tm''
resolveTerm CnsRep (CST.CoLambda loc fv tm) =
  do
    tm' <- resolveTerm CnsRep tm
    let tm'' = RST.termClosing [(Cns,fv)] tm'
    return $ RST.Lambda loc CnsRep fv tm''
resolveTerm rep (CST.FunApp loc fun arg) =
  resolveApp rep loc fun arg
resolveTerm PrdRep (CST.CoLambda loc _fv _tm) =
  throwOtherError loc ["Cannot resolve Cofunction to a producer."]
resolveTerm CnsRep (CST.Lambda loc _fv _tm) =
  throwOtherError loc ["Cannot resolve Function to a consumer."]
---------------------------------------------------------------------------------
-- CST constructs which can only be resolved to commands
---------------------------------------------------------------------------------
resolveTerm _ (CST.Apply loc _ _) =
  throwOtherError loc ["Cannot resolve Apply command to a term."]
resolveTerm _ CST.PrimTerm {} =
  throwOtherError defaultLoc [" Cannot resolve primTerm to a term."]
