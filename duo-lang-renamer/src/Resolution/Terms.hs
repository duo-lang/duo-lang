{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant multi-way if" #-}
module Resolution.Terms (resolveTerm, resolveCommand, resolveInstanceCase) where

import Control.Monad (when, forM)
import Control.Monad.Except (throwError)
import Data.Bifunctor ( second )
import Data.Text qualified as T

import Errors.Renamer
import Resolution.Definition
import Resolution.SymbolTable
import Resolution.Pattern
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCns(..), Arity, PrdCnsRep(..))
import Syntax.CST.Names
import Syntax.RST.Names
import Loc
import qualified Syntax.LocallyNameless as LN
import Data.Either (fromLeft, isLeft)
import Resolution.Types (resolveTyp)
import Syntax.RST.Types (PolarityRep(..))

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

data IntermediateCase  pat = MkIntermediateCase
  { icase_loc  :: Loc
  , icase_pat  :: pat
  , icase_term :: CST.Term
  }

type SomeIntermediateCase = IntermediateCase (Either RST.PatternNew RST.StarPattern)

data Cases where
  ExplicitCases    :: [IntermediateCase RST.PatternNew]  -> Cases
  ImplicitPrdCases :: [IntermediateCase RST.StarPattern] -> Cases
  ImplicitCnsCases :: [IntermediateCase RST.StarPattern] -> Cases

starPatternToPrdCns :: RST.StarPattern -> PrdCns
starPatternToPrdCns (RST.PatStar _ pc) = case pc of Prd -> Cns; Cns -> Prd
starPatternToPrdCns (RST.PatXtorStar _ _ _ _ (_, sp,_)) = starPatternToPrdCns sp

isExplicitCase :: SomeIntermediateCase -> Bool
isExplicitCase icase = isLeft icase.icase_pat

isImplicitCase :: PrdCns -> SomeIntermediateCase -> Bool
isImplicitCase pc icase =
  case icase.icase_pat of
    Left _ -> False
    Right pat -> pc == starPatternToPrdCns pat

fromExplicitCase :: SomeIntermediateCase -> IntermediateCase RST.PatternNew
fromExplicitCase cs = cs { icase_pat = fromLeft undefined cs.icase_pat }

fromImplicitCase :: SomeIntermediateCase -> IntermediateCase RST.StarPattern
fromImplicitCase cs =
  case cs.icase_pat of
    Left _ -> undefined
    Right pat -> cs { icase_pat = pat}

adjustPat :: (Loc, PrdCns, FreeVarName) -> (PrdCns, FreeVarName)
adjustPat (_loc, pc, var) = (pc,var)

analyzeCase :: CST.DataCodata
            -- ^ Whether a constructor (Data) or destructor (Codata) is expected in this case
            -> CST.TermCase
            -> ResolverM SomeIntermediateCase
analyzeCase dc tmcase = do
  analyzedPattern <- resolvePattern (case dc of CST.Data -> Prd ; CST.Codata -> Cns) tmcase.pat
  pure $ MkIntermediateCase { icase_loc = tmcase.loc
                            , icase_pat = analyzedPattern
                            , icase_term = tmcase.term
                            }

analyzeCases :: CST.DataCodata
             -> [CST.TermCase]
             -> ResolverM Cases
analyzeCases dc cases = do
  cases' <- mapM (analyzeCase dc) cases
  if | all isExplicitCase cases' -> pure $ ExplicitCases    $ fromExplicitCase <$> cases'
     | all (isImplicitCase Prd) cases' -> pure $ ImplicitPrdCases $ fromImplicitCase <$> cases'
     | all (isImplicitCase Cns) cases' -> pure $ ImplicitCnsCases $ fromImplicitCase <$> cases'
     | otherwise -> throwError (UnknownResolutionError (getLoc (head cases)) "Cases mix the use of both explicit and implicit patterns.")

---------------------------------------------------------------------------------
-- Resolve Cases
---------------------------------------------------------------------------------

newPatToPat :: RST.PatternNew -> ResolverM (RST.Pattern, [(PrdCns, FreeVarName)])
newPatToPat (RST.PatXtor loc _pc _ns xt pats) = do
  pats' <- fmap adjustPat <$> mapM fromVar pats
  let pat = RST.XtorPat loc xt (second Just <$> pats')
  pure (pat, pats')
newPatToPat pat = throwError (UnknownResolutionError (getLoc pat) "This pattern is not supported yet")

resolveCommandCase :: IntermediateCase RST.PatternNew-> ResolverM RST.CmdCase
resolveCommandCase icase = do
  cmd' <- resolveCommand icase.icase_term
  (pat, args) <- newPatToPat icase.icase_pat
  pure RST.MkCmdCase { cmdcase_loc = icase.icase_loc
                     , cmdcase_pat = pat
                     , cmdcase_cmd = LN.close args cmd'
                     }
resolveTermCase :: PrdCnsRep pc -> IntermediateCase RST.PatternNew -> ResolverM (RST.TermCase pc)
resolveTermCase rep icase = do
  tm' <- resolveTerm rep icase.icase_term
  (pat, args) <- newPatToPat icase.icase_pat
  pure RST.MkTermCase { tmcase_loc  = icase.icase_loc
                      , tmcase_pat = pat
                      , tmcase_term = LN.close args tm'
                      }

starPatToPatternI :: RST.StarPattern -> ResolverM (RST.PatternI, [(PrdCns, FreeVarName)])
starPatToPatternI (RST.PatXtorStar loc pc _ns xt (patl,RST.PatStar _ Cns,patr)) = do
  patl' <- fmap adjustPat <$> mapM fromVar patl
  patr' <- fmap adjustPat <$> mapM fromVar patr
  let pat = RST.XtorPatI loc xt (second Just <$> patl',(), second Just <$> patr')
  let args = patl' ++ [(case pc of Prd -> Cns; Cns -> Prd,MkFreeVarName "*")] ++ patr'
  pure (pat, args)
starPatToPatternI pat = throwError (UnknownResolutionError (getLoc pat) "This star pattern is not supported yet.")

resolveTermCaseI :: PrdCnsRep pc -> IntermediateCase RST.StarPattern -> ResolverM (RST.TermCaseI pc)
resolveTermCaseI rep icase = do
  tm' <- resolveTerm rep icase.icase_term
  (pat, args) <- starPatToPatternI icase.icase_pat
  pure RST.MkTermCaseI { tmcasei_loc = icase.icase_loc
                       , tmcasei_pat = pat
                       , tmcasei_term = LN.close args tm'
                       }

---------------------------------------------------------------------------------
-- Resolving InstanceCases
---------------------------------------------------------------------------------

resolveInstanceCase :: CST.TermCase -> ResolverM RST.InstanceCase
resolveInstanceCase tmcase = do
  (_,xt,pat) <- analyzeInstancePattern tmcase.pat
  let pat' = adjustPat <$> pat
  cmd' <- resolveCommand tmcase.term
  pure RST.MkInstanceCase { instancecase_loc = tmcase.loc
                          , instancecase_pat = RST.XtorPat tmcase.loc xt (second Just <$> pat')
                          , instancecase_cmd = LN.close pat' cmd'
                          }

---------------------------------------------------------------------------------
-- Resolving PrimCommands
---------------------------------------------------------------------------------

resolvePrimCommand :: Loc -> PrimName -> CST.Substitution -> ResolverM RST.Command
-- 0 arguments
resolvePrimCommand loc nm (CST.MkSubstitution []) =
  if | nm == exitSuccessName -> pure $ RST.ExitSuccess loc
     | nm == exitFailureName -> pure $ RST.ExitFailure loc
     | otherwise             -> throwError (PrimOpArityMismatch loc nm 0)
-- 1 argument
resolvePrimCommand loc nm (CST.MkSubstitution [tm]) | nm == readName =
  if | nm == readName -> do
               tm' <- resolveTerm CnsRep tm
               pure $ RST.Read loc tm'
     | otherwise      -> throwError (PrimOpArityMismatch loc nm 1)
-- 2 arguments
resolvePrimCommand loc nm (CST.MkSubstitution [tm, cmd]) | nm == printName = do
  tm' <- resolveTerm PrdRep tm
  cmd' <- resolveCommand cmd
  pure $ RST.Print loc tm' cmd'
--3 arguments
resolvePrimCommand loc nm (CST.MkSubstitution [tm1,tm2,tm3]) = do
  tm1' <- resolveTerm PrdRep tm1
  tm2' <- resolveTerm PrdRep tm2
  tm3' <- resolveTerm CnsRep tm3
  let args = RST.MkSubstitution [RST.PrdTerm tm1', RST.PrdTerm tm2', RST.CnsTerm tm3']
  if | nm == i64AddName -> pure (RST.PrimOp loc RST.I64Add args)
     | nm == i64SubName -> pure (RST.PrimOp loc RST.I64Sub args)
     | nm == i64MulName -> pure (RST.PrimOp loc RST.I64Mul args)
     | nm == i64DivName -> pure (RST.PrimOp loc RST.I64Div args)
     | nm == i64ModName -> pure (RST.PrimOp loc RST.I64Mod args)
     | nm == f64AddName -> pure (RST.PrimOp loc RST.F64Add args)
     | nm == f64SubName -> pure (RST.PrimOp loc RST.F64Sub args)
     | nm == f64MulName -> pure (RST.PrimOp loc RST.F64Mul args)
     | nm == f64DivName -> pure (RST.PrimOp loc RST.F64Div args)
     | nm == charPrependName -> pure (RST.PrimOp loc RST.CharPrepend args)
     | nm == stringAppendName -> pure (RST.PrimOp loc RST.StringAppend args)
     | otherwise -> throwError (PrimOpArityMismatch loc nm 3)
-- More arguments
resolvePrimCommand loc nm args = throwError (PrimOpArityMismatch loc nm (length args.unSubstitution))

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
      cmdCases <- mapM resolveCommandCase explicitCases
      pure $ RST.CaseOfCmd loc ns tm' cmdCases
    ImplicitPrdCases implicitCases -> do
      termCasesI <- mapM (resolveTermCaseI PrdRep) implicitCases
      pure $ RST.CaseOfI loc PrdRep ns tm' termCasesI
    ImplicitCnsCases implicitCases -> do
      termCasesI <- mapM (resolveTermCaseI CnsRep) implicitCases
      pure $ RST.CaseOfI loc CnsRep ns tm' termCasesI
resolveCommand (CST.CocaseOf loc tm cases) = do
  tm' <- resolveTerm CnsRep tm
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cmdCases <- mapM resolveCommandCase explicitCases
      pure $ RST.CocaseOfCmd loc ns tm' cmdCases
    ImplicitPrdCases implicitCases -> do
      termCasesI <- mapM (resolveTermCaseI PrdRep) implicitCases
      pure $ RST.CocaseOfI loc PrdRep ns tm' termCasesI
    ImplicitCnsCases implicitCases -> do
      termCasesI <- mapM (resolveTermCaseI CnsRep) implicitCases
      pure $ RST.CocaseOfI loc CnsRep ns tm' termCasesI
resolveCommand (CST.Xtor loc xtor ty arity) = do
  (_, res) <- lookupXtor loc xtor
  case res of
    (XtorNameResult _dc _ns _ar) -> throwError (CmdExpected loc "Method (Command) expected, but found Xtor")
    (MethodNameResult cn ar) -> do
      let mn = MkMethodName xtor.unXtorName
      analyzedSubst <- analyzeMethodSubstitution loc mn cn ar arity
      subst' <- case analyzedSubst of
          ExplicitSubst es -> return (map snd es)
          ImplicitSubst {} ->  throwError (UnknownResolutionError loc "The substitution in a method call cannot contain implicit arguments")
      pctms <- resolveTerms loc ar subst'
      ty' <- mapM (\ty' -> resolveTyp PosRep ty' >>= \typ -> resolveTyp NegRep ty' >>= \tyn -> pure (typ, tyn)) ty
      pure $ RST.Method loc mn cn ty' (RST.MkSubstitution pctms)
---------------------------------------------------------------------------------
-- CST constructs which can only be resolved to commands
---------------------------------------------------------------------------------
resolveCommand (CST.Semi loc _ _ _) =
  throwError (CmdExpected loc "Command expected, but found Semi")
resolveCommand (CST.Dtor loc _ _ _) =
  throwError (CmdExpected loc "Command expected, but found Dtor")
resolveCommand (CST.Case loc _) =
  throwError (CmdExpected loc "Command expected, but found Case")
resolveCommand (CST.Cocase loc _) =
  throwError (CmdExpected loc "Command expected, but found Cocase")
resolveCommand (CST.MuAbs loc _ _) =
  throwError (CmdExpected loc "Command expected, but found Mu abstraction")
resolveCommand (CST.PrimLitI64 loc _) =
  throwError (CmdExpected loc "Command expected, but found #I64 literal")
resolveCommand (CST.PrimLitF64 loc _) =
  throwError (CmdExpected loc "Command expected, but found #F64 literal")
resolveCommand (CST.PrimLitChar loc _) =
  throwError (CmdExpected loc "Command expected, but found #Char literal")
resolveCommand (CST.PrimLitString loc _) =
  throwError (CmdExpected loc "Command expected, but found #String literal")
resolveCommand (CST.NatLit loc _ _) =
  throwError (CmdExpected loc "Command expected, but found Nat literal")
resolveCommand (CST.FunApp loc _ _) =
  throwError (CmdExpected loc "Command expected, but found function application")
resolveCommand (CST.Lambda loc _ _) =
  throwError (CmdExpected loc "Command expected, but found lambda abstraction")
resolveCommand (CST.CoLambda loc _ _) =
  throwError (CmdExpected loc "Command expected, but found cofunction abstraction")


casesToNS :: [CST.TermCase] -> ResolverM RST.NominalStructural
casesToNS [] = pure RST.Structural
casesToNS (tmcase:_) = 
  case tmcase.pat of
    CST.PatXtor _ name _ -> do
      (_, XtorNameResult _ ns _) <- lookupXtor tmcase.loc name
      pure ns
    _ ->
      throwError (UnknownResolutionError defaultLoc "casesToNS called with invalid argument")

-- | Lower a natural number literal.
resolveNatLit :: Loc -> CST.NominalStructural -> Int -> ResolverM (RST.Term Prd)
resolveNatLit loc ns 0 = pure $ RST.Xtor loc PrdRep (RST.cstToRstNS ns (MkTypeName "Nat")) (MkXtorName "Z") (RST.MkSubstitution [])
resolveNatLit loc ns n = do
  n' <- resolveNatLit loc ns (n-1)
  pure $ RST.Xtor loc PrdRep (RST.cstToRstNS ns (MkTypeName "Nat")) (MkXtorName "S") (RST.MkSubstitution [RST.PrdTerm n'])

-- | Lower an application.
resolveApp :: PrdCnsRep pc -> Loc -> CST.Term -> CST.Term -> ResolverM (RST.Term pc)
resolveApp PrdRep loc fun arg = do
  fun' <- resolveTerm PrdRep fun
  arg' <- resolveTerm PrdRep arg
  pure $ RST.Dtor loc PrdRep (RST.Nominal (MkTypeName "Fun")) (MkXtorName "Ap") fun' (RST.MkSubstitutionI ([RST.PrdTerm arg'],PrdRep,[]))
resolveApp CnsRep loc fun arg = do
  fun' <- resolveTerm CnsRep fun
  arg' <- resolveTerm CnsRep arg
  pure $ RST.Semi loc CnsRep (RST.Nominal (MkTypeName "CoFun")) (MkXtorName "CoAp")  (RST.MkSubstitutionI ([RST.CnsTerm arg'],CnsRep,[])) fun'

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

analyzeSubstitution :: Loc -> Arity -> CST.SubstitutionI -> ResolverM AnalyzedSubstitution
analyzeSubstitution loc arity (CST.MkSubstitutionI subst) = do
  -- Dispatch on the number of stars in the substitution
  case length (filter isStarT subst) of
    0 -> pure $ ExplicitSubst (zip arity (toTm <$> subst))
    1 -> do
      let zipped :: [(PrdCns, CST.TermOrStar)] = zip arity subst
      case break (isStarT . snd) zipped of
        (subst1,(pc,_):subst2) -> pure $ ImplicitSubst (second toTm <$> subst1) pc (second toTm <$> subst2)
        _ -> throwError (UnknownResolutionError loc "Compiler bug in analyzeSubstitution")
    n -> throwError (UnknownResolutionError loc ("At most one star expected. Got " <> T.pack (show n) <> " stars."))

analyzeXtorSubstitution :: Loc -> XtorName -> Arity -> CST.SubstitutionI -> ResolverM AnalyzedSubstitution
analyzeXtorSubstitution loc xtor arity subst = do
  -- Check whether the arity corresponds to the length of the substitution
  when (length arity /= length subst.unSubstitutionI) $
    throwError (XtorArityMismatch loc xtor (length arity) (length subst.unSubstitutionI))
  analyzeSubstitution loc arity subst

analyzeMethodSubstitution :: Loc -> MethodName -> ClassName -> Arity -> CST.SubstitutionI -> ResolverM AnalyzedSubstitution
analyzeMethodSubstitution loc mn cn arity subst = do
  -- Check whether the arity corresponds to the length of the substitution
  when (length arity /= length subst.unSubstitutionI) $
    throwError (MethodArityMismatch loc mn cn (length arity) (length subst.unSubstitutionI))
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
  pure $ RST.MuAbs loc PrdRep (Just fv) (LN.close [(Cns,fv)] cmd')
resolveTerm CnsRep (CST.MuAbs loc fv cmd) = do
  cmd' <- resolveCommand cmd
  pure $ RST.MuAbs loc CnsRep (Just fv) (LN.close [(Prd,fv)] cmd')
---------------------------------------------------------------------------------
-- Xtor
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.Xtor loc xtor _ty subst) = do
  (_, res) <- lookupXtor loc xtor
  case res of
    (XtorNameResult dc ns ar) -> do
      when (length ar /= length subst.unSubstitutionI) $
               throwError (XtorArityMismatch loc xtor (length ar) (length subst.unSubstitutionI))
      when (dc /= CST.Data) $
               throwError (UnknownResolutionError loc ("The given xtor " <> T.pack (show xtor) <> " is declared as a destructor, not a constructor."))
      analyzedSubst <- analyzeXtorSubstitution loc xtor ar subst
      subst' <- case analyzedSubst of
          ExplicitSubst es -> return (map snd es)
          ImplicitSubst {} ->  throwError (UnknownResolutionError loc "The substitution in a constructor call cannot contain implicit arguments")
      pctms <- resolveTerms loc ar subst'
      pure $ RST.Xtor loc PrdRep ns xtor (RST.MkSubstitution pctms)
    (MethodNameResult _cn _ar) -> throwError (UnknownResolutionError loc "Xtor expected, but found Method")
resolveTerm CnsRep (CST.Xtor loc xtor _ty subst) = do
  (_, res) <- lookupXtor loc xtor
  case res of
    (XtorNameResult dc ns ar) -> do
      when (length ar /= length subst.unSubstitutionI) $
               throwError (XtorArityMismatch loc xtor (length ar) (length subst.unSubstitutionI))
      when (dc /= CST.Codata) $
               throwError (UnknownResolutionError loc ("The given xtor " <> T.pack (show xtor) <> " is declared as a constructor, not a destructor."))
      analyzedSubst <- analyzeXtorSubstitution loc xtor ar subst
      subst' <- case analyzedSubst of
          ExplicitSubst es -> return (map snd es)
          ImplicitSubst {} ->  throwError (UnknownResolutionError loc "The substitution in a constructor call cannot contain implicit arguments")
      pctms <- resolveTerms loc ar subst'
      pure $ RST.Xtor loc CnsRep ns xtor (RST.MkSubstitution pctms)
    (MethodNameResult _cn _ar) -> throwError (UnknownResolutionError loc "Xtor expected, but found Method")
---------------------------------------------------------------------------------
-- Semi / Dtor
---------------------------------------------------------------------------------
resolveTerm rep (CST.Semi loc xtor subst tm) = do
  tm' <- resolveTerm CnsRep tm
  (_, XtorNameResult dc ns ar) <- lookupXtor loc xtor
  when (dc /= CST.Data) $
           throwError (UnknownResolutionError loc ("The given xtor " <> T.pack (show xtor) <> " is declared as a destructor, not a constructor."))
  analyzedSubst <- analyzeXtorSubstitution loc xtor ar subst
  case analyzedSubst of
    ExplicitSubst _explicitSubst -> do
      throwError (UnknownResolutionError loc "The substitution in a Semi must contain at least one implicit argument")
    ImplicitSubst subst1 Prd subst2 -> do
      case rep of
        PrdRep ->
          throwError (UnknownResolutionError loc "Tried to resolve Semi to a producer, but implicit argument stands for a producer")
        CnsRep -> do
          subst1' <- forM subst1 $ uncurry resolvePrdCnsTerm
          subst2' <- forM subst2 $ uncurry resolvePrdCnsTerm
          pure $ RST.Semi loc CnsRep ns xtor (RST.MkSubstitutionI (subst1', CnsRep, subst2')) tm'
    ImplicitSubst subst1 Cns subst2 -> do
      case rep of
        PrdRep -> do
          subst1' <- forM subst1 $ uncurry resolvePrdCnsTerm
          subst2' <- forM subst2 $ uncurry resolvePrdCnsTerm
          pure $ RST.Semi loc PrdRep ns xtor (RST.MkSubstitutionI (subst1', PrdRep, subst2')) tm'
        CnsRep ->
          throwError (UnknownResolutionError loc "Tried to resolve Semi to a producer, but implicit argument stands for a producer")
resolveTerm rep (CST.Dtor loc xtor tm subst) = do
  tm' <- resolveTerm PrdRep tm
  (_, XtorNameResult dc ns ar) <- lookupXtor loc xtor
  when (dc /= CST.Codata) $
           throwError (UnknownResolutionError loc ("The given xtor " <> T.pack (show xtor) <> " is declared as a constructor, not a destructor."))
  analyzedSubst <- analyzeXtorSubstitution loc xtor ar subst
  case analyzedSubst of
    ExplicitSubst _explicitSubst -> do
      throwError (UnknownResolutionError loc "The substitution in a dtor must contain at least one implicit argument")
    ImplicitSubst subst1 Prd subst2 -> do
      case rep of
        PrdRep -> do
          throwError (UnknownResolutionError loc "Tried to resolve Dtor to a producer, but implicit argument stands for a producer")
        CnsRep -> do
          subst1' <- forM subst1 $ uncurry resolvePrdCnsTerm
          subst2' <- forM subst2 $ uncurry resolvePrdCnsTerm
          pure $ RST.Dtor loc CnsRep ns xtor tm' (RST.MkSubstitutionI (subst1', CnsRep, subst2'))
    ImplicitSubst subst1 Cns subst2 -> do
      case rep of
        PrdRep -> do
          subst1' <- forM subst1 $ uncurry resolvePrdCnsTerm
          subst2' <- forM subst2 $ uncurry resolvePrdCnsTerm
          pure $ RST.Dtor loc PrdRep ns xtor tm' (RST.MkSubstitutionI (subst1', PrdRep, subst2'))
        CnsRep -> do
          throwError (UnknownResolutionError loc "Tried to resolve Dtor to a consumer, but implicit argument stands for consumer")
---------------------------------------------------------------------------------
-- Case / Cocase
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.Case loc _) =
  throwError (UnknownResolutionError loc "Cannot resolve pattern match to a producer.")
resolveTerm CnsRep (CST.Cocase loc _) =
  throwError (UnknownResolutionError loc "Cannot resolve copattern match to a consumer.")
resolveTerm PrdRep (CST.Cocase loc cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- mapM resolveCommandCase explicitCases
      pure $ RST.XCase loc PrdRep ns cases'
    ImplicitPrdCases implicitCases -> do
      cases' <- mapM (resolveTermCaseI PrdRep) implicitCases
      pure $ RST.CocaseI loc PrdRep ns cases'
    ImplicitCnsCases implicitCases -> do
      cases' <- mapM (resolveTermCaseI CnsRep) implicitCases
      pure $ RST.CocaseI loc CnsRep ns cases'
resolveTerm CnsRep (CST.Case loc cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- mapM resolveCommandCase explicitCases
      pure $ RST.XCase loc CnsRep ns cases'
    ImplicitPrdCases implicitCases -> do
      cases' <- mapM (resolveTermCaseI PrdRep) implicitCases
      pure $ RST.CaseI loc PrdRep ns cases'
    ImplicitCnsCases implicitCases -> do
      cases' <- mapM (resolveTermCaseI CnsRep) implicitCases
      pure $ RST.CaseI loc CnsRep ns cases'
---------------------------------------------------------------------------------
-- CaseOf / CocaseOf
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.CaseOf loc t cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- mapM (resolveTermCase PrdRep) explicitCases
      t' <- resolveTerm PrdRep t
      pure $ RST.CaseOf loc PrdRep ns t' cases'
    ImplicitPrdCases _implicitCases ->
      throwError (UnknownResolutionError loc "Cannot resolve case-of with implicit cases to producer.")
    ImplicitCnsCases _implicitCases ->
      throwError (UnknownResolutionError loc "Cannot resolve case-of with implicit cases to producer.")
resolveTerm PrdRep (CST.CocaseOf loc t cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- mapM (resolveTermCase PrdRep) explicitCases
      t' <- resolveTerm CnsRep t
      pure $ RST.CocaseOf loc PrdRep ns t' cases'
    ImplicitPrdCases _implicitCases ->
      throwError (UnknownResolutionError loc "Cannot resolve cocase-of with implicit cases to producer")
    ImplicitCnsCases _implicitCases ->
      throwError (UnknownResolutionError loc "Cannot resolve cocase-of with implicit cases to producer")
resolveTerm CnsRep (CST.CaseOf loc t cases) = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- mapM (resolveTermCase CnsRep) explicitCases
      t' <- resolveTerm PrdRep t
      pure $ RST.CaseOf loc CnsRep ns t' cases'
    ImplicitPrdCases _implicitCases ->
      throwError (UnknownResolutionError loc "Cannot resolve case-of with implicit cases to consumer.")
    ImplicitCnsCases _implicitCases ->
      throwError (UnknownResolutionError loc "Cannot resolve case-of with implicit cases to consumer.")
resolveTerm CnsRep (CST.CocaseOf loc t cases) = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases CST.Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- mapM (resolveTermCase CnsRep) explicitCases
      t' <- resolveTerm CnsRep t
      pure $ RST.CocaseOf loc CnsRep ns t' cases'
    ImplicitPrdCases _implicitCases ->
      throwError (UnknownResolutionError loc "Cannot resolve cocase-of with implicit cases to consumer")
    ImplicitCnsCases _implicitCases ->
      throwError (UnknownResolutionError loc "Cannot resolve cocase-of with implicit cases to consumer")
---------------------------------------------------------------------------------
-- Literals
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.PrimLitI64 loc i) =
  pure $ RST.PrimLitI64 loc i
resolveTerm CnsRep (CST.PrimLitI64 loc _) =
  throwError (UnknownResolutionError loc "Cannot resolve primitive literal to a consumer.")
resolveTerm PrdRep (CST.PrimLitF64 loc d) =
  pure $ RST.PrimLitF64 loc d
resolveTerm CnsRep (CST.PrimLitF64 loc _) =
  throwError (UnknownResolutionError loc "Cannot resolve primitive literal to a consumer.")
resolveTerm PrdRep (CST.PrimLitChar loc d) =
  pure $ RST.PrimLitChar loc d
resolveTerm CnsRep (CST.PrimLitChar loc _) =
  throwError (UnknownResolutionError loc "Cannot resolve primitive literal to a consumer.")
resolveTerm PrdRep (CST.PrimLitString loc d) =
  pure $ RST.PrimLitString loc d
resolveTerm CnsRep (CST.PrimLitString loc _) =
  throwError (UnknownResolutionError loc "Cannot resolve primitive literal to a consumer.")
resolveTerm PrdRep (CST.NatLit loc ns i) =
  resolveNatLit loc ns i
resolveTerm CnsRep (CST.NatLit loc _ns _i) =
  throwError (UnknownResolutionError loc "Cannot resolve NatLit to a consumer.")
---------------------------------------------------------------------------------
-- Function specific syntax sugar
---------------------------------------------------------------------------------
resolveTerm PrdRep (CST.Lambda loc fv tm) =
  do
    tm' <- resolveTerm PrdRep tm
    let tm'' = LN.close [(Prd,fv)] tm'
    return $ RST.Lambda loc PrdRep fv tm''
resolveTerm CnsRep (CST.CoLambda loc fv tm) =
  do
    tm' <- resolveTerm CnsRep tm
    let tm'' = LN.close [(Cns,fv)] tm'
    return $ RST.Lambda loc CnsRep fv tm''
resolveTerm rep (CST.FunApp loc fun arg) =
  resolveApp rep loc fun arg
resolveTerm PrdRep (CST.CoLambda loc _fv _tm) =
  throwError (UnknownResolutionError loc "Cannot resolve Cofunction to a producer.")
resolveTerm CnsRep (CST.Lambda loc _fv _tm) =
  throwError (UnknownResolutionError loc "Cannot resolve Function to a consumer.")
---------------------------------------------------------------------------------
-- CST constructs which can only be resolved to commands
---------------------------------------------------------------------------------
resolveTerm _ (CST.Apply loc _ _) =
  throwError (UnknownResolutionError loc "Cannot resolve Apply command to a term.")
resolveTerm _ CST.PrimTerm {} =
  throwError (UnknownResolutionError defaultLoc " Cannot resolve primTerm to a term.")
