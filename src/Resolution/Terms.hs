module Resolution.Terms (resolveTerm, resolveCommand, resolveInstanceCase) where

import Control.Monad (when, forM)
import Control.Monad.Except (throwError)
import Data.Bifunctor ( second )
import Data.Map qualified as M
import Data.Text qualified as T

import Errors
import Pretty.Pretty ( ppPrint )
import Resolution.Definition
import Resolution.SymbolTable
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Terms qualified as CST
import Syntax.Common
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
-- Analyze Patterns
---------------------------------------------------------------------------------

data AnalyzedPattern
  = ExplicitPattern Loc XtorName [(PrdCns, FreeVarName)]
  | ImplicitPrdPattern Loc XtorName ([(PrdCns, FreeVarName)], PrdCnsRep Prd,[(PrdCns,FreeVarName)])
  | ImplicitCnsPattern Loc XtorName ([(PrdCns, FreeVarName)], PrdCnsRep Cns,[(PrdCns,FreeVarName)])

analyzePattern :: DataCodata -> CST.TermPat -> ResolverM AnalyzedPattern
analyzePattern dc (CST.XtorPat loc xt args) = do
  -- Lookup up the arity information in the symbol table.
  (_,XtorNameResult dc' _ arity) <- lookupXtor loc xt
  -- Check whether the Xtor is a Constructor/Destructor as expected.
  case (dc,dc') of
    (Codata,Data  ) -> throwError $ OtherError (Just loc) "Expected a destructor but found a constructor"
    (Data  ,Codata) -> throwError $ OtherError (Just loc) "Expected a constructor but found a destructor"
    (Data  ,Data  ) -> pure ()
    (Codata,Codata) -> pure ()
  -- Analyze the pattern
  -- Check whether the number of arguments in the given binding site
  -- corresponds to the number of arguments specified for the constructor/destructor.
  when (length arity /= length args) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch xt (length arity) (length args)
  case length (filter CST.isStar args) of
    0 -> pure $ ExplicitPattern loc xt $ zip arity (CST.fromFVOrStar <$> args)
    1 -> do
      let zipped :: [(PrdCns, CST.FVOrStar)] = zip arity args
      let (args1,(pc,_):args2) = break (\(_,x) -> CST.isStar x) zipped
      case pc of
        Cns -> pure $ ImplicitPrdPattern loc xt (second CST.fromFVOrStar <$> args1, PrdRep, second CST.fromFVOrStar <$> args2)
        Prd -> pure $ ImplicitCnsPattern loc xt (second CST.fromFVOrStar <$> args1, CnsRep, second CST.fromFVOrStar <$> args2)
    n -> throwError $ LowerError (Just loc) $ InvalidStar ("More than one star used in binding site: " <> T.pack (show n) <> " stars used.")

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

-- Refines `CST.TermCase` to either `IntermediateCase` or `IntermediateCaseI`, depending on
-- the number of stars.
analyzeCase :: DataCodata
            -- ^ Whether a constructor (Data) or destructor (Codata) is expected in this case
            -> CST.TermCase
            -> ResolverM SomeIntermediateCase
analyzeCase dc CST.MkTermCase { tmcase_loc, tmcase_pat, tmcase_term } = do
  analyzedPattern <- analyzePattern dc tmcase_pat
  case analyzedPattern of
    ExplicitPattern _ xt pat -> pure $ ExplicitCase $ MkIntermediateCase
                                    { icase_loc = tmcase_loc
                                    , icase_name = xt
                                    , icase_args = pat
                                    , icase_term = tmcase_term
                                    }
    ImplicitPrdPattern _ xt pat -> pure $ ImplicitCase PrdRep $ MkIntermediateCaseI
                                    { icasei_loc = tmcase_loc
                                    , icasei_name = xt
                                    , icasei_args = pat
                                    , icasei_term = tmcase_term
                                    }
    ImplicitCnsPattern _ xt pat -> pure $ ImplicitCase CnsRep $ MkIntermediateCaseI
                                    { icasei_loc = tmcase_loc
                                    , icasei_name = xt
                                    , icasei_args = pat
                                    , icasei_term = tmcase_term
                                    }

analyzeCases :: DataCodata
             -> [CST.TermCase]
             -> ResolverM SomeIntermediateCases
analyzeCases dc cases = do
  cases' <- sequence $ analyzeCase dc <$> cases
  if | all isExplicitCase cases' -> pure $ ExplicitCases    $ fromExplicitCase <$> cases'
     | all (isImplicitCase PrdRep) cases' -> pure $ ImplicitCases PrdRep $ fromImplicitCase PrdRep <$> cases'
     | all (isImplicitCase CnsRep) cases' -> pure $ ImplicitCases CnsRep $ fromImplicitCase CnsRep <$> cases'
     | otherwise -> throwError $ OtherError Nothing "Cases mix the use of both explicit and implicit patterns."

analyzeInstancePattern :: CST.InstancePat -> ResolverM AnalyzedPattern
analyzeInstancePattern (CST.MethodPat loc m args) = do
  let xt :: XtorName
      xt = MkXtorName $ unMethodName m
  (_,MethodNameResult _cn arity) <- lookupXtor loc xt
  when (length arity /= length args) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch undefined (length arity) (length args)
  pure $ ExplicitPattern loc xt $ zip arity (CST.fromFVOrStar <$> args)
  
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

resolveInstanceCase :: CST.InstanceCase -> ResolverM (RST.InstanceCase Cns)
resolveInstanceCase (CST.MkInstanceCase loc pat t) = do
  intermediateCase <- analyzeInstancePattern pat
  case intermediateCase of
    (ExplicitPattern loc' xtor args) -> do
      tm' <- resolveTerm CnsRep t
      pure RST.MkInstanceCase { instancecase_loc  = loc
                              , instancecase_pat = RST.XtorPat loc' xtor (second Just <$> args)
                              , instancecase_term = RST.termClosing args tm'
                              }
    _ -> throwError (OtherError Nothing "Expected explicit patterns in instance definition.")

---------------------------------------------------------------------------------
-- Resolving PrimCommands
---------------------------------------------------------------------------------

getPrimOpArity :: Loc -> (PrimitiveType, PrimitiveOp) -> ResolverM Arity
getPrimOpArity loc primOp = do
  case M.lookup primOp primOps of
    Nothing -> throwError $ LowerError (Just loc) $ UndefinedPrimOp primOp
    Just aritySpecified -> return aritySpecified

resolvePrimCommand :: CST.PrimCommand -> ResolverM RST.Command
resolvePrimCommand (CST.Print loc tm cmd) = do
  tm' <- resolveTerm PrdRep tm
  cmd' <- resolveCommand cmd
  pure $ RST.Print loc tm' cmd'
resolvePrimCommand (CST.Read loc tm) = do
  tm' <- resolveTerm CnsRep tm
  pure $ RST.Read loc tm'
resolvePrimCommand (CST.ExitSuccess loc) =
  pure $ RST.ExitSuccess loc
resolvePrimCommand (CST.ExitFailure loc) =
  pure $ RST.ExitFailure loc
resolvePrimCommand (CST.PrimOp loc pt op args) = do
  reqArity <- getPrimOpArity loc (pt, op)
  when (length reqArity /= length args) $
         throwError $ LowerError (Just loc) $ PrimOpArityMismatch (pt,op) (length reqArity) (length args)
  args' <- resolveTerms loc reqArity args
  pure $ RST.PrimOp loc pt op args'

---------------------------------------------------------------------------------
-- Resolving Commands
---------------------------------------------------------------------------------

resolveCommand :: CST.Term -> ResolverM RST.Command
resolveCommand (CST.TermParens _loc cmd) =
  resolveCommand cmd
resolveCommand (CST.Var loc fv) =
  pure $ RST.Jump loc fv
resolveCommand (CST.PrimCmdTerm cmd) =
  resolvePrimCommand cmd
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
  intermediateCases <- analyzeCases Data cases
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
  intermediateCases <- analyzeCases Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cmdCases <- sequence $ resolveCommandCase <$> explicitCases
      pure $ RST.CocaseOfCmd loc ns tm' cmdCases
    ImplicitCases rep implicitCases -> do
      termCasesI <- sequence $ resolveTermCaseI rep <$> implicitCases
      pure $ RST.CocaseOfI loc rep ns tm' termCasesI
---------------------------------------------------------------------------------
-- CST constructs which can only be resolved to commands
---------------------------------------------------------------------------------
resolveCommand (CST.Xtor loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Xtor")
resolveCommand (CST.Semi loc _ _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Semi")
resolveCommand (CST.Dtor loc _ _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Dtor")
resolveCommand (CST.Case loc _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Case")
resolveCommand (CST.Cocase loc _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Cocase")
resolveCommand (CST.MuAbs loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Mu abstraction")
resolveCommand (CST.PrimLitI64 loc _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found #I64 literal")
resolveCommand (CST.PrimLitF64 loc _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found #F64 literal")
resolveCommand (CST.NatLit loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Nat literal")
resolveCommand (CST.FunApp loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found function application")
resolveCommand (CST.Lambda loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found lambda abstraction")
resolveCommand (CST.CoLambda loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found cofunction abstraction")



casesToNS :: [CST.TermCase] -> ResolverM NominalStructural
casesToNS [] = pure Structural
casesToNS (CST.MkTermCase { tmcase_loc, tmcase_pat = CST.XtorPat _ tmcase_name _ }:_) = do
  (_, XtorNameResult _ ns _) <- lookupXtor tmcase_loc tmcase_name
  pure ns


-- | Lower a natural number literal.
resolveNatLit :: Loc -> NominalStructural -> Int -> ResolverM (RST.Term Prd)
resolveNatLit loc ns 0 = pure $ RST.Xtor loc PrdRep ns (MkXtorName "Z") []
resolveNatLit loc ns n = do
  n' <- resolveNatLit loc ns (n-1)
  pure $ RST.Xtor loc PrdRep ns (MkXtorName "S") [RST.PrdTerm n']

-- | Lower an application.
resolveApp :: PrdCnsRep pc -> Loc -> CST.Term -> CST.Term -> ResolverM (RST.Term pc)
resolveApp PrdRep loc fun arg = do
  fun' <- resolveTerm PrdRep fun
  arg' <- resolveTerm PrdRep arg
  pure $ RST.Dtor loc PrdRep Nominal (MkXtorName "Ap") fun' ([RST.PrdTerm arg'],PrdRep,[])
resolveApp CnsRep loc fun arg = do
  fun' <- resolveTerm CnsRep fun
  arg' <- resolveTerm CnsRep arg
  pure $ RST.Semi loc CnsRep Nominal (MkXtorName "CoAp")  ([RST.CnsTerm arg'],CnsRep,[]) fun'

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

analyzeSubstitution :: Loc -> XtorName -> Arity -> [CST.TermOrStar] -> ResolverM AnalyzedSubstitution
analyzeSubstitution loc xtor arity subst = do
  -- Check whether the arity corresponds to the length of the substitution
  when (length arity /= length subst) $
    throwError $ LowerError (Just loc) $ XtorArityMismatch xtor (length arity) (length subst)
  -- Dispatch on the number of stars in the substitution
  case length (filter isStarT subst) of
    0 -> pure $ ExplicitSubst (zip arity (toTm <$> subst))
    1 -> do
      let zipped :: [(PrdCns, CST.TermOrStar)] = zip arity subst
      case span (not . isStarT . snd) zipped of
        (subst1,(pc,_):subst2) -> pure $ ImplicitSubst (second toTm <$> subst1) pc (second toTm <$> subst2)
        _ -> throwError $ OtherError (Just loc) "Compiler bug in analyzeSubstitution"
    n -> throwError $ OtherError (Just loc) ("At most one star expected. Got " <> T.pack (show n) <> " stars.")

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
  (_, XtorNameResult dc ns ar) <- lookupXtor loc xtor
  when (length ar /= length subst) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch xtor (length ar) (length subst)
  when (dc /= Data) $
           throwError $ OtherError (Just loc) ("The given xtor " <> ppPrint xtor <> " is declared as a destructor, not a constructor.")
  analyzedSubst <- analyzeSubstitution loc xtor ar subst
  subst' <- case analyzedSubst of
      ExplicitSubst es -> return (map snd es)
      ImplicitSubst {} ->  throwError (OtherError (Just loc) "The substitution in a constructor call cannot contain implicit arguments")
  pctms <- resolveTerms loc ar subst'
  pure $ RST.Xtor loc PrdRep ns xtor pctms
resolveTerm CnsRep (CST.Xtor loc xtor subst) = do
  (_, XtorNameResult dc ns ar) <- lookupXtor loc xtor
  when (length ar /= length subst) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch xtor (length ar) (length subst)
  when (dc /= Codata) $
           throwError $ OtherError (Just loc) ("The given xtor " <> ppPrint xtor <> " is declared as a constructor, not a destructor.")
  analyzedSubst <- analyzeSubstitution loc xtor ar subst
  subst' <- case analyzedSubst of
      ExplicitSubst es -> return (map snd es)
      ImplicitSubst {} ->  throwError (OtherError (Just loc) "The substitution in a constructor call cannot contain implicit arguments")
  pctms <- resolveTerms loc ar subst'
  pure $ RST.Xtor loc CnsRep ns xtor pctms
---------------------------------------------------------------------------------
-- Semi / Dtor
---------------------------------------------------------------------------------
resolveTerm rep (CST.Semi loc xtor subst tm) = do
  tm' <- resolveTerm CnsRep tm
  (_, XtorNameResult dc ns ar) <- lookupXtor loc xtor
  when (dc /= Data) $
           throwError $ OtherError (Just loc) ("The given xtor " <> ppPrint xtor <> " is declared as a destructor, not a constructor.")
  analyzedSubst <- analyzeSubstitution loc xtor ar subst
  case analyzedSubst of
    ExplicitSubst _explicitSubst -> do
      throwError (OtherError (Just loc) "The substitution in a Semi must contain at least one implicit argument")
    ImplicitSubst subst1 Prd subst2 -> do
      case rep of
        PrdRep ->
          throwError (OtherError (Just loc) "Tried to resolve Semi to a producer, but implicit argument stands for a producer")
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
          throwError (OtherError (Just loc) "Tried to resolve Semi to a producer, but implicit argument stands for a producer")
resolveTerm rep (CST.Dtor loc xtor tm subst) = do
  tm' <- resolveTerm PrdRep tm
  (_, XtorNameResult dc ns ar) <- lookupXtor loc xtor
  when (dc /= Codata) $
           throwError $ OtherError (Just loc) ("The given xtor " <> ppPrint xtor <> " is declared as a constructor, not a destructor.")
  analyzedSubst <- analyzeSubstitution loc xtor ar subst
  case analyzedSubst of
    ExplicitSubst _explicitSubst -> do
      throwError (OtherError (Just loc) "The substitution in a dtor must contain at least one implicit argument")
    ImplicitSubst subst1 Prd subst2 -> do
      case rep of
        PrdRep -> do
          throwError (OtherError (Just loc) "Tried to resolve Dtor to a producer, but implicit argument stands for a producer")
        CnsRep -> do
          subst1' <- forM subst1 $ uncurry resolvePrdCnsTerm
          subst2' <- forM subst2 $ uncurry resolvePrdCnsTerm
          pure $ RST.Dtor loc CnsRep ns xtor tm' (subst1', CnsRep, subst2')
    ImplicitSubst subst1 Cns subst2 -> do
      case rep of
        PrdRep -> do
          subst1' <- forM subst1 $ uncurry resolvePrdCnsTerm
          subst2' <- forM subst2 $ \(pc,tm) -> resolvePrdCnsTerm pc tm
          pure $ RST.Dtor loc PrdRep ns xtor tm' (subst1', PrdRep, subst2')
        CnsRep -> do
          throwError (OtherError (Just loc) "Tried to resolve Dtor to a consumer, but implicit argument stands for consumer")
---------------------------------------------------------------------------------
-- Case / Cocase
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.Case loc _) =
  throwError (OtherError (Just loc) "Cannot resolve pattern match to a producer.")
resolveTerm CnsRep (CST.Cocase loc _) =
  throwError (OtherError (Just loc) "Cannot resolve copattern match to a consumer.")
resolveTerm PrdRep (CST.Cocase loc cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence $ resolveCommandCase <$> explicitCases
      pure $ RST.XCase loc PrdRep ns cases'
    ImplicitCases rep implicitCases -> do
      cases' <- sequence $ resolveTermCaseI rep <$> implicitCases
      pure $ RST.CocaseI loc rep ns cases'
resolveTerm CnsRep (CST.Case loc cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Data cases
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
  intermediateCases <- analyzeCases Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (resolveTermCase PrdRep <$> explicitCases)
      t' <- resolveTerm PrdRep t
      pure $ RST.CaseOf loc PrdRep ns t' cases'
    ImplicitCases _rep _implicitCases ->
      throwError $ OtherError (Just loc) "Cannot resolve case-of with implicit cases to producer."
resolveTerm PrdRep (CST.CocaseOf loc t cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (resolveTermCase PrdRep <$> explicitCases)
      t' <- resolveTerm CnsRep t
      pure $ RST.CocaseOf loc PrdRep ns t' cases'
    ImplicitCases _rep _implicitCases ->
      throwError $ OtherError (Just loc) "Cannot resolve cocase-of with implicit cases to producer"
resolveTerm CnsRep (CST.CaseOf loc t cases) = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (resolveTermCase CnsRep <$> explicitCases)
      t' <- resolveTerm PrdRep t
      pure $ RST.CaseOf loc CnsRep ns t' cases'
    ImplicitCases _rep _implicitCases ->
      throwError $ OtherError (Just loc) "Cannot resolve case-of with implicit cases to consumer."
resolveTerm CnsRep (CST.CocaseOf loc t cases) = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (resolveTermCase CnsRep <$> explicitCases)
      t' <- resolveTerm CnsRep t
      pure $ RST.CocaseOf loc CnsRep ns t' cases'
    ImplicitCases _rep _implicitCases ->
      throwError $ OtherError (Just loc) "Cannot resolve cocase-of with implicit cases to consumer"
---------------------------------------------------------------------------------
-- Literals
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.PrimLitI64 loc i) =
  pure $ RST.PrimLitI64 loc i
resolveTerm CnsRep (CST.PrimLitI64 loc _) =
  throwError (OtherError (Just loc) "Cannot resolve primitive literal to a consumer.")
resolveTerm PrdRep (CST.PrimLitF64 loc d) =
  pure $ RST.PrimLitF64 loc d
resolveTerm CnsRep (CST.PrimLitF64 loc _) =
  throwError (OtherError (Just loc) "Cannot resolve primitive literal to a consumer.")
resolveTerm PrdRep (CST.NatLit loc ns i) =
  resolveNatLit loc ns i
resolveTerm CnsRep (CST.NatLit loc _ns _i) =
  throwError (OtherError (Just loc) "Cannot resolve NatLit to a consumer.")
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
  throwError (OtherError (Just loc) "Cannot resolve Cofunction to a producer.")
resolveTerm CnsRep (CST.Lambda loc _fv _tm) =
  throwError (OtherError (Just loc) "Cannot resolve Function to a consumer.")
---------------------------------------------------------------------------------
-- CST constructs which can only be resolved to commands
---------------------------------------------------------------------------------
resolveTerm _ (CST.Apply loc _ _) =
  throwError (OtherError (Just loc) "Cannot resolve Apply command to a term.")
resolveTerm _ (CST.PrimCmdTerm _) =
  throwError (OtherError Nothing " Cannot resolve primCmdTerm to a term.")
