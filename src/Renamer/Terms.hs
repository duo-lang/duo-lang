module Renamer.Terms (renameTerm, renameCommand) where

import Control.Monad.Except (throwError)
import Data.Bifunctor ( second )
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map qualified as M
import Text.Megaparsec.Pos (SourcePos)

import Errors
import Renamer.Definition
import Renamer.SymbolTable
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Terms qualified as CST
import Syntax.Common
import Utils
import Control.Monad (when)
import qualified Data.Text as T

---------------------------------------------------------------------------------
-- Check Arity of Xtor
---------------------------------------------------------------------------------

-- can only be called when length ar == length tms
renameTerms :: Loc -> Arity -> [CST.Term] -> RenamerM [RST.PrdCnsTerm]
renameTerms _ [] [] = return []
renameTerms loc (Prd:ar) (t:tms) = do
  t' <- RST.PrdTerm <$> renameTerm PrdRep t
  tms' <- renameTerms loc ar tms
  pure $ t' : tms'
renameTerms loc (Cns:ar) (t:tms) = do
  t' <- RST.CnsTerm <$> renameTerm CnsRep t
  tms' <- renameTerms loc ar tms
  pure $ t' : tms'
renameTerms loc ar t = error $ "compiler bug in renameTerms, loc = " ++ show loc ++ ", ar = " ++ show ar ++ ", t = " ++ show t

---------------------------------------------------------------------------------
-- Analyze cases
---------------------------------------------------------------------------------

data AnalyzedPattern
  = ExplicitPattern [(PrdCns, FreeVarName)]
  | ImplicitPrdPattern ([(PrdCns, FreeVarName)], PrdCnsRep Prd,[(PrdCns,FreeVarName)])
  | ImplicitCnsPattern ([(PrdCns, FreeVarName)], PrdCnsRep Cns,[(PrdCns,FreeVarName)])

analyzePattern :: Loc -> Arity -> [CST.FVOrStar] -> RenamerM AnalyzedPattern
analyzePattern loc arity pattern = do
  -- Check whether the number of arguments in the given binding site
  -- corresponds to the number of arguments specified for the constructor/destructor.
  when (length arity /= length pattern) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch undefined (length arity) (length pattern)
  case length (filter CST.isStar pattern) of
    0 -> pure $ ExplicitPattern $ zip arity (CST.fromFVOrStar <$> pattern)
    1 -> do
      let zipped :: [(PrdCns, CST.FVOrStar)] = zip arity pattern
      let (args1,((pc,_):args2)) = break (\(_,x) -> CST.isStar x) zipped
      case pc of
        Cns -> pure $ ImplicitPrdPattern (second CST.fromFVOrStar <$> args1, PrdRep, second CST.fromFVOrStar <$> args2)
        Prd -> pure $ ImplicitCnsPattern (second CST.fromFVOrStar <$> args1, CnsRep, second CST.fromFVOrStar <$> args2)
    n -> throwError $ LowerError (Just loc) $ InvalidStar ("More than one star used in binding site: " <> T.pack (show n) <> " stars used.")

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
            -> RenamerM SomeIntermediateCase
analyzeCase dc (CST.MkTermCase { tmcase_loc, tmcase_name, tmcase_args, tmcase_term }) = do
  -- Lookup up the arity information in the symbol table.
  (_,XtorNameResult dc' _ arity) <- lookupXtor tmcase_loc tmcase_name
  -- Check whether the Xtor is a Constructor/Destructor as expected.
  case (dc,dc') of
    (Codata,Data  ) -> throwError $ OtherError (Just tmcase_loc) "Expected a destructor but found a constructor"
    (Data  ,Codata) -> throwError $ OtherError (Just tmcase_loc) "Expected a constructor but found a destructor"
    (Data  ,Data  ) -> pure ()
    (Codata,Codata) -> pure ()
  -- Analyze the pattern
  analyzedPattern <- analyzePattern tmcase_loc arity tmcase_args
  case analyzedPattern of
    ExplicitPattern pat -> pure $ ExplicitCase $ MkIntermediateCase
                                    { icase_loc = tmcase_loc
                                    , icase_name = tmcase_name
                                    , icase_args = pat
                                    , icase_term = tmcase_term
                                    }
    ImplicitPrdPattern pat -> pure $ ImplicitCase PrdRep $ MkIntermediateCaseI
                                    { icasei_loc = tmcase_loc
                                    , icasei_name = tmcase_name
                                    , icasei_args = pat
                                    , icasei_term = tmcase_term
                                    }
    ImplicitCnsPattern pat -> pure $ ImplicitCase CnsRep $ MkIntermediateCaseI
                                    { icasei_loc = tmcase_loc
                                    , icasei_name = tmcase_name
                                    , icasei_args = pat
                                    , icasei_term = tmcase_term
                                    }



analyzeCases :: DataCodata
             -> [CST.TermCase]
             -> RenamerM SomeIntermediateCases
analyzeCases dc cases = do
  cases' <- sequence $ analyzeCase dc <$> cases
  if | all isExplicitCase cases' -> pure $ ExplicitCases    $ fromExplicitCase <$> cases'
     | all (isImplicitCase PrdRep) cases' -> pure $ ImplicitCases PrdRep $ fromImplicitCase PrdRep <$> cases'
     | all (isImplicitCase CnsRep) cases' -> pure $ ImplicitCases CnsRep $ fromImplicitCase CnsRep <$> cases'
     | otherwise -> throwError $ OtherError Nothing "Cases mix the use of both explicit and implicit patterns."


---------------------------------------------------------------------------------
-- Rename Cases
---------------------------------------------------------------------------------

renameCommandCase :: IntermediateCase -> RenamerM RST.CmdCase
renameCommandCase MkIntermediateCase { icase_loc , icase_name , icase_args , icase_term } = do
  cmd' <- renameCommand icase_term
  pure RST.MkCmdCase { cmdcase_loc = icase_loc
                     , cmdcase_name = icase_name
                     , cmdcase_args = second Just <$> icase_args
                     , cmdcase_cmd = RST.commandClosing icase_args cmd'
                     }

renameTermCaseI :: PrdCnsRep pc -> IntermediateCaseI pc -> RenamerM (RST.TermCaseI pc)
renameTermCaseI rep MkIntermediateCaseI { icasei_loc, icasei_name, icasei_args = (args1,_, args2), icasei_term } = do
  tm' <- renameTerm rep icasei_term
  pure RST.MkTermCaseI { tmcasei_loc = icasei_loc
                       , tmcasei_name = icasei_name
                       , tmcasei_args = (second Just <$> args1, (), second Just <$> args2)
                       , tmcasei_term = RST.termClosing (args1 ++ [(Cns, MkFreeVarName "*")] ++ args2) tm'
                       }

renameTermCase :: PrdCnsRep pc -> IntermediateCase -> RenamerM (RST.TermCase pc)
renameTermCase rep MkIntermediateCase { icase_loc, icase_name, icase_args, icase_term } = do
  tm' <- renameTerm rep icase_term
  pure RST.MkTermCase { tmcase_loc  = icase_loc
                      , tmcase_name = icase_name
                      , tmcase_args = second Just <$> icase_args
                      , tmcase_term = RST.termClosing icase_args tm'
                      }

---------------------------------------------------------------------------------
-- Renaming PrimCommands
---------------------------------------------------------------------------------

getPrimOpArity :: Loc -> (PrimitiveType, PrimitiveOp) -> RenamerM Arity
getPrimOpArity loc primOp = do
  case M.lookup primOp primOps of
    Nothing -> throwError $ LowerError (Just loc) $ UndefinedPrimOp primOp
    Just aritySpecified -> return aritySpecified

renamePrimCommand :: CST.PrimCommand -> RenamerM RST.Command
renamePrimCommand (CST.Print loc tm cmd) = do
  tm' <- renameTerm PrdRep tm
  cmd' <- renameCommand cmd
  pure $ RST.Print loc tm' cmd'
renamePrimCommand (CST.Read loc tm) = do
  tm' <- renameTerm CnsRep tm
  pure $ RST.Read loc tm'
renamePrimCommand (CST.ExitSuccess loc) =
  pure $ RST.ExitSuccess loc
renamePrimCommand (CST.ExitFailure loc) =
  pure $ RST.ExitFailure loc
renamePrimCommand (CST.PrimOp loc pt op args) = do
  reqArity <- getPrimOpArity loc (pt, op)
  when (length reqArity /= length args) $
         throwError $ LowerError (Just loc) $ PrimOpArityMismatch (pt,op) (length reqArity) (length args)
  args' <- renameTerms loc reqArity args
  pure $ RST.PrimOp loc pt op args'

---------------------------------------------------------------------------------
-- Renaming Commands
---------------------------------------------------------------------------------

renameCommand :: CST.Term -> RenamerM RST.Command
renameCommand (CST.TermParens _loc cmd) =
  renameCommand cmd
renameCommand (CST.Var loc fv) =
  pure $ RST.Jump loc fv
renameCommand (CST.PrimCmdTerm cmd) =
  renamePrimCommand cmd
renameCommand (CST.Apply loc tm1 tm2) = do
  tm1' <- renameTerm PrdRep tm1
  tm2' <- renameTerm CnsRep tm2
  pure $ RST.Apply loc tm1' tm2'
---------------------------------------------------------------------------------
-- CaseOf / CocaseOf
---------------------------------------------------------------------------------
renameCommand (CST.CaseOf loc tm cases) = do
  tm' <- renameTerm PrdRep tm
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cmdCases <- sequence $ renameCommandCase <$> explicitCases
      pure $ RST.CaseOfCmd loc ns tm' cmdCases
    ImplicitCases rep implicitCases -> do
      termCasesI <- sequence $ renameTermCaseI rep <$> implicitCases
      pure $ RST.CaseOfI loc rep ns tm' termCasesI
renameCommand (CST.CocaseOf loc tm cases) = do
  tm' <- renameTerm CnsRep tm
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cmdCases <- sequence $ renameCommandCase <$> explicitCases
      pure $ RST.CocaseOfCmd loc ns tm' cmdCases
    ImplicitCases rep implicitCases -> do
      termCasesI <- sequence $ renameTermCaseI rep <$> implicitCases
      pure $ RST.CocaseOfI loc rep ns tm' termCasesI
---------------------------------------------------------------------------------
-- CST constructs which can only be renamed to commands
---------------------------------------------------------------------------------
renameCommand (CST.Xtor loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Xtor")
renameCommand (CST.Semi loc _ _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Semi")
renameCommand (CST.Dtor loc _ _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Dtor")
renameCommand (CST.Case loc _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Case")
renameCommand (CST.Cocase loc _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Cocase")
renameCommand (CST.MuAbs loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Mu abstraction")
renameCommand (CST.PrimLitI64 loc _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found #I64 literal")
renameCommand (CST.PrimLitF64 loc _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found #F64 literal")
renameCommand (CST.NatLit loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Nat literal")
renameCommand (CST.DtorChain _ _ _) =
  throwError $ LowerError Nothing (CmdExpected "Command expected, but found DtorChain")
renameCommand (CST.FunApp loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found function application")
renameCommand (CST.MultiLambda loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found lambda abstraction")
renameCommand (CST.Lambda loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found lambda abstraction")



casesToNS :: [CST.TermCase] -> RenamerM NominalStructural
casesToNS [] = pure Structural
casesToNS ((CST.MkTermCase { tmcase_loc, tmcase_name }):_) = do
  (_, XtorNameResult _ ns _) <- lookupXtor tmcase_loc tmcase_name
  pure ns

-- | Lower a multi-lambda abstraction
renameMultiLambda :: Loc -> [FreeVarName] -> CST.Term -> RenamerM (CST.Term)
renameMultiLambda _ [] tm = pure tm
renameMultiLambda loc (fv:fvs) tm = CST.Lambda loc fv <$> renameMultiLambda loc fvs tm

-- | Lower a lambda abstraction.
renameLambda :: Loc -> FreeVarName -> CST.Term -> RenamerM (RST.Term Prd)
renameLambda loc var tm = do
  tm' <- renameTerm PrdRep tm
  pure $ RST.CocaseI loc PrdRep Nominal [ RST.MkTermCaseI loc (MkXtorName "Ap")
                                                      ([(Prd, Just var)], (), [])
                                                      (RST.termClosing [(Prd, var)] tm')
                                    ]

-- | Lower a natural number literal.
renameNatLit :: Loc -> NominalStructural -> Int -> RenamerM (RST.Term Prd)
renameNatLit loc ns 0 = pure $ RST.Xtor loc PrdRep ns (MkXtorName "Z") []
renameNatLit loc ns n = do
  n' <- renameNatLit loc ns (n-1)
  pure $ RST.Xtor loc PrdRep ns (MkXtorName "S") [RST.PrdTerm n']

-- | Lower an application.
renameApp :: Loc -> CST.Term -> CST.Term -> RenamerM (RST.Term Prd)
renameApp loc fun arg = do
  fun' <- renameTerm PrdRep fun
  arg' <- renameTerm PrdRep arg
  pure $ RST.Dtor loc PrdRep Nominal (MkXtorName "Ap") fun' ([RST.PrdTerm arg'],PrdRep,[])

isStarT :: CST.TermOrStar -> Bool
isStarT CST.ToSStar  = True
isStarT _ = False

toTm  :: CST.TermOrStar -> CST.Term
toTm (CST.ToSTerm t) = t
toTm _x = error "Compiler bug: toFV"

renameDtorChain :: SourcePos -> CST.Term -> NonEmpty (XtorName, [CST.TermOrStar], SourcePos) -> RenamerM CST.Term
renameDtorChain startPos tm ((xtor, subst, endPos) :| [])   = pure $ CST.Dtor (Loc startPos endPos) xtor tm subst
renameDtorChain startPos tm ((xtor, subst, endPos) :| (x:xs)) = renameDtorChain startPos (CST.Dtor (Loc startPos endPos) xtor tm subst) (x :| xs)

split :: Loc -> [CST.TermOrStar] -> RenamerM ([CST.Term],[CST.Term])
split loc args = do
  let numstars = length (filter isStarT args)
  when ( numstars /= 1) $ throwError (OtherError (Just loc) "Exactly one star expected" )
  let (args1,_:args2) = span (not . isStarT) args
  return (map toTm args1,map toTm args2)


renameTerm :: PrdCnsRep pc -> CST.Term -> RenamerM (RST.Term pc)
renameTerm rep (CST.TermParens _loc tm) =
  renameTerm rep tm
renameTerm rep (CST.Var loc v) =
  pure $ RST.FreeVar loc rep v
---------------------------------------------------------------------------------
-- Mu abstraction
---------------------------------------------------------------------------------
renameTerm PrdRep (CST.MuAbs loc fv cmd) = do
  cmd' <- renameCommand cmd
  pure $ RST.MuAbs loc PrdRep (Just fv) (RST.commandClosing [(Cns,fv)] cmd')
renameTerm CnsRep (CST.MuAbs loc fv cmd) = do
  cmd' <- renameCommand cmd
  pure $ RST.MuAbs loc CnsRep (Just fv) (RST.commandClosing [(Prd,fv)] cmd')
---------------------------------------------------------------------------------
-- Xtor
---------------------------------------------------------------------------------
renameTerm PrdRep (CST.Xtor loc xtor subst) = do
  (_, XtorNameResult dc ns ar) <- lookupXtor loc xtor
  when (length ar /= length subst) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch xtor (length ar) (length subst)
  when (dc /= Data) $
           throwError $ OtherError (Just loc) "The given xtor is declared as a destructor, not a constructor."
  pctms <- renameTerms loc ar subst
  pure $ RST.Xtor loc PrdRep ns xtor pctms
renameTerm CnsRep (CST.Xtor loc xtor subst) = do
  (_, XtorNameResult dc ns ar) <- lookupXtor loc xtor
  when (length ar /= length subst) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch xtor (length ar) (length subst)
  when (dc /= Codata) $
           throwError $ OtherError (Just loc) "The given xtor is declared as a constructor, not a destructor."
  pctms <- renameTerms loc ar subst
  pure $ RST.Xtor loc CnsRep ns xtor pctms
---------------------------------------------------------------------------------
-- Semi / Dtor
---------------------------------------------------------------------------------
renameTerm _ (CST.Semi _loc _xtor _subst _c) =
  error "renameTerm / Semi: not yet implemented"
renameTerm rep    (CST.DtorChain pos tm dtors) =
  renameDtorChain pos tm dtors >>= renameTerm rep
renameTerm PrdRep (CST.Dtor loc xtor tm subst) = do
  (_, XtorNameResult _ ns ar) <- lookupXtor loc xtor
  when (length ar /= length subst) $
           throwError $ LowerError (Just loc) $ XtorArityMismatch xtor (length ar) (length subst)
  tm' <- renameTerm PrdRep tm
  (args1,args2) <- split loc subst
  let (ar1,_:ar2) = splitAt (length args1) ar
  -- there must be exactly one star
  args1' <- renameTerms loc ar1 args1
  args2' <- renameTerms loc ar2 args2
  pure $ RST.Dtor loc PrdRep ns xtor tm' (args1',PrdRep,args2')
renameTerm CnsRep (CST.Dtor loc _xtor _tm _s)   =
  throwError (OtherError (Just loc) "Cannot rename Dtor to a consumer (TODO).")
---------------------------------------------------------------------------------
-- Case / Cocase
---------------------------------------------------------------------------------
renameTerm PrdRep (CST.Case loc _) =
  throwError (OtherError (Just loc) "Cannot rename pattern match to a producer.")
renameTerm CnsRep (CST.Cocase loc _) =
  throwError (OtherError (Just loc) "Cannot rename copattern match to a consumer.")
renameTerm PrdRep (CST.Cocase loc cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence $ renameCommandCase <$> explicitCases
      pure $ RST.XCase loc PrdRep ns cases'
    ImplicitCases rep implicitCases -> do
      cases' <- sequence $ renameTermCaseI rep <$> implicitCases
      pure $ RST.CocaseI loc rep ns cases'
renameTerm CnsRep (CST.Case loc cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence $ renameCommandCase <$> explicitCases
      pure $ RST.XCase loc CnsRep ns cases'
    ImplicitCases rep implicitCases -> do
      cases' <- sequence $ renameTermCaseI rep <$> implicitCases
      pure $ RST.CaseI loc rep ns cases'
---------------------------------------------------------------------------------
-- CaseOf / CocaseOf
---------------------------------------------------------------------------------
renameTerm PrdRep (CST.CaseOf loc t cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (renameTermCase PrdRep <$> explicitCases)
      t' <- renameTerm PrdRep t
      pure $ RST.CaseOf loc PrdRep ns t' cases'
    ImplicitCases _rep _implicitCases ->
      throwError $ OtherError (Just loc) "Cannot rename case-of with implicit cases to producer."
renameTerm PrdRep (CST.CocaseOf loc t cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (renameTermCase PrdRep <$> explicitCases)
      t' <- renameTerm CnsRep t
      pure $ RST.CocaseOf loc PrdRep ns t' cases'
    ImplicitCases _rep _implicitCases ->
      throwError $ OtherError (Just loc) "Cannot rename cocase-of with implicit cases to producer"
renameTerm CnsRep (CST.CaseOf loc t cases) = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (renameTermCase CnsRep <$> explicitCases)
      t' <- renameTerm PrdRep t
      pure $ RST.CaseOf loc CnsRep ns t' cases'
    ImplicitCases _rep _implicitCases ->
      throwError $ OtherError (Just loc) "Cannot rename case-of with implicit cases to consumer."
renameTerm CnsRep (CST.CocaseOf loc t cases) = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (renameTermCase CnsRep <$> explicitCases)
      t' <- renameTerm CnsRep t
      pure $ RST.CocaseOf loc CnsRep ns t' cases'
    ImplicitCases _rep _implicitCases ->
      throwError $ OtherError (Just loc) "Cannot rename cocase-of with implicit cases to consumer"
---------------------------------------------------------------------------------
-- Literals
---------------------------------------------------------------------------------
renameTerm PrdRep (CST.PrimLitI64 loc i) =
  pure $ RST.PrimLitI64 loc i
renameTerm CnsRep (CST.PrimLitI64 loc _) =
  throwError (OtherError (Just loc) "Cannot rename primitive literal to a consumer.")
renameTerm PrdRep (CST.PrimLitF64 loc d) =
  pure $ RST.PrimLitF64 loc d
renameTerm CnsRep (CST.PrimLitF64 loc _) =
  throwError (OtherError (Just loc) "Cannot rename primitive literal to a consumer.")
renameTerm PrdRep (CST.NatLit loc ns i) =
  renameNatLit loc ns i
renameTerm CnsRep (CST.NatLit loc _ns _i) =
  throwError (OtherError (Just loc) "Cannot rename NatLit to a consumer.")
---------------------------------------------------------------------------------
-- Function specific syntax sugar
---------------------------------------------------------------------------------
renameTerm rep    (CST.MultiLambda loc fvs tm) =
  renameMultiLambda loc fvs tm >>= renameTerm rep
renameTerm PrdRep (CST.FunApp loc fun arg) =
  renameApp loc fun arg
renameTerm CnsRep (CST.FunApp loc _fun _arg) =
  throwError (OtherError (Just loc) "Cannot rename FunApp to a consumer.")
renameTerm PrdRep (CST.Lambda loc fv tm) =
  renameLambda loc fv tm
renameTerm CnsRep (CST.Lambda loc _fv _tm) =
  throwError (OtherError (Just loc) "Cannot rename Lambda to a consumer.")
---------------------------------------------------------------------------------
-- CST constructs which can only be renamed to commands
---------------------------------------------------------------------------------
renameTerm _ (CST.Apply loc _ _) = 
  throwError (OtherError (Just loc) "Cannot rename Apply command to a term.")
renameTerm _ (CST.PrimCmdTerm _) =
  throwError (OtherError Nothing " Cannot rename primCmdTerm to a term.")
