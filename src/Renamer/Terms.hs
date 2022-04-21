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

renameT :: PrdCns -> CST.Term -> RenamerM RST.PrdCnsTerm
renameT Prd t = RST.PrdTerm <$> renameTerm PrdRep t
renameT Cns t = RST.CnsTerm <$> renameTerm CnsRep t

-- can only be called when length ar == length tms
renameTerms :: Loc -> Arity -> [CST.Term] -> RenamerM [RST.PrdCnsTerm]
renameTerms _ [] [] = return []
renameTerms loc (a:ar) (t:tms) = do
  t' <- renameT a t
  tms' <- renameTerms loc ar tms
  return $ t' : tms'
renameTerms loc ar t = error $ "compiler bug in renameTerms, loc = " ++ show loc ++ ", ar = " ++ show ar ++ ", t = " ++ show t

---------------------------------------------------------------------------------
-- Analyze cases
---------------------------------------------------------------------------------

splitFS :: [CST.FVOrStar] -> ([FreeVarName], PrdCnsRep Prd, [FreeVarName])
splitFS args = (map (\(CST.FoSFV fv) -> fv) args1, PrdRep, map (\(CST.FoSFV fv) -> fv) args2)
  where
    (args1,(_:args2)) = break CST.isStar args

-- | A case with no stars.
data IntermediateCase  = MkIntermediateCase
  { icase_loc  :: Loc
  , icase_name :: XtorName
  , icase_args :: [FreeVarName]
  , icase_term :: CST.Term
  }

-- | A case with exactly one star.
data IntermediateCaseI pc = MkIntermediateCaseI
  { icasei_loc  :: Loc
  , icasei_name :: XtorName
  , icasei_args :: ([FreeVarName], PrdCnsRep pc, [FreeVarName])
  , icasei_term :: CST.Term
  }

data SomeIntermediateCase where
  ExplicitCase    :: IntermediateCase      -> SomeIntermediateCase
  ImplicitPrdCase :: IntermediateCaseI Prd -> SomeIntermediateCase
  ImplicitCnsCase :: IntermediateCaseI Cns -> SomeIntermediateCase

isExplicitCase :: SomeIntermediateCase -> Bool
isExplicitCase (ExplicitCase _) = True
isExplicitCase _                = False

isImplicitPrdCase :: SomeIntermediateCase -> Bool
isImplicitPrdCase (ImplicitPrdCase _) = True
isImplicitPrdCase _                   = False

isImplicitCnsCase :: SomeIntermediateCase -> Bool
isImplicitCnsCase (ImplicitCnsCase _) = True
isImplicitCnsCase _                   = False

fromExplicitCase :: SomeIntermediateCase -> IntermediateCase
fromExplicitCase (ExplicitCase cs) = cs
fromExplicitCase _                 = error "Compiler bug"

fromImplicitPrdCase :: SomeIntermediateCase -> IntermediateCaseI Prd
fromImplicitPrdCase (ImplicitPrdCase cs) = cs
fromImplicitPrdCase _                    = error "Compiler bug"

fromImplicitCnsCase :: SomeIntermediateCase -> IntermediateCaseI Cns
fromImplicitCnsCase (ImplicitCnsCase cs) = cs
fromImplicitCnsCase _                    = error "Compiler bug"


data SomeIntermediateCases where
  ExplicitCases    :: [IntermediateCase]      -> SomeIntermediateCases
  ImplicitPrdCases :: [IntermediateCaseI Prd] -> SomeIntermediateCases
  ImplicitCnsCases :: [IntermediateCaseI Cns] -> SomeIntermediateCases

-- Refines `CST.TermCase` to either `IntermediateCase` or `IntermediateCaseI`, depending on
-- the number of stars.
analyzeCase :: DataCodata
            -- ^ Whether a constructor (Data) or destructor (Codata) is expected in this case
            -> CST.TermCase
            -> RenamerM SomeIntermediateCase
analyzeCase dc (CST.MkTermCase { tmcase_loc, tmcase_name, tmcase_args, tmcase_term }) = do
  -- Lookup up the arity information in the symbol table.
  (_,XtorNameResult dc' _ arity) <- lookupXtor tmcase_loc tmcase_name
  -- Check whether the number of arguments in the given binding site
  -- corresponds to the number of arguments specified for the constructor/destructor.
  when (length arity /= length tmcase_args) $
           throwError $ LowerError (Just tmcase_loc) $ XtorArityMismatch tmcase_name (length arity) (length tmcase_args)
  -- Check whether the Xtor is a Constructor/Destructor as expected.
  case (dc,dc') of
    (Codata,Data  ) -> throwError $ OtherError (Just tmcase_loc) "Expected a destructor but found a constructor"
    (Data  ,Codata) -> throwError $ OtherError (Just tmcase_loc) "Expected a constructor but found a destructor"
    (Data  ,Data  ) -> pure ()
    (Codata,Codata) -> pure ()
  -- Do a case-distinction based on the number of arguments
  case length (filter CST.isStar tmcase_args) of
    0 -> pure $ ExplicitCase $ MkIntermediateCase
                        { icase_loc = tmcase_loc
                        , icase_name = tmcase_name
                        , icase_args = CST.fromFVOrStar <$> tmcase_args
                        , icase_term = tmcase_term
                        }
    1 -> pure $ ImplicitPrdCase $ MkIntermediateCaseI
                        { icasei_loc = tmcase_loc
                        , icasei_name = tmcase_name
                        , icasei_args = splitFS tmcase_args
                        , icasei_term = tmcase_term
                        }
    n -> throwError $ LowerError (Just tmcase_loc) $ InvalidStar ("More than one star used in binding site: " <> T.pack (show n) <> " stars used.")

fromEitherList :: [SomeIntermediateCase] -> RenamerM (SomeIntermediateCases)
fromEitherList ls | all isExplicitCase ls    = pure $ ExplicitCases    $ fromExplicitCase <$> ls
                  | all isImplicitPrdCase ls = pure $ ImplicitPrdCases $ fromImplicitPrdCase <$> ls
                  | all isImplicitCnsCase ls = pure $ ImplicitCnsCases $ fromImplicitCnsCase <$> ls
                  | otherwise = error "TODO: write error message"

analyzeCases :: DataCodata
             -> [CST.TermCase]
             -> RenamerM SomeIntermediateCases
analyzeCases dc cases = do
  cases' <- sequence $ analyzeCase dc <$> cases
  fromEitherList cases'

---------------------------------------------------------------------------------
-- Rename Cases
---------------------------------------------------------------------------------

renameCommandCase :: IntermediateCase -> RenamerM RST.CmdCase
renameCommandCase MkIntermediateCase { icase_loc , icase_name , icase_args , icase_term } = do
  cmd' <- renameCommand icase_term
  (_,XtorNameResult _ _ ar) <- lookupXtor icase_loc icase_name
  let args = zip ar icase_args
  pure RST.MkCmdCase { cmdcase_loc = icase_loc
                     , cmdcase_name = icase_name
                     , cmdcase_args = second Just <$> args
                     , cmdcase_cmd = RST.commandClosing args cmd'
                     }

renameTermCaseI :: PrdCnsRep pc -> IntermediateCaseI pc -> RenamerM (RST.TermCaseI pc)
renameTermCaseI rep MkIntermediateCaseI { icasei_loc, icasei_name, icasei_args = (args1,_, args2), icasei_term } = do
  tm' <- renameTerm rep icasei_term
  (_, XtorNameResult _ _ ar) <- lookupXtor icasei_loc icasei_name
  let (ar1,_:ar2) = splitAt (length args1) ar
  let args1' = zip ar1 args1
  let args2' = zip ar2 args2
  pure RST.MkTermCaseI { tmcasei_loc = icasei_loc
                       , tmcasei_name = icasei_name
                       , tmcasei_args = (second Just <$> args1', (), second Just <$> args2')
                       , tmcasei_term = RST.termClosing (args1' ++ [(Cns, MkFreeVarName "*")] ++ args2') tm'
                       }

renameTermCase :: PrdCnsRep pc -> IntermediateCase -> RenamerM (RST.TermCase pc)
renameTermCase rep MkIntermediateCase { icase_loc, icase_name, icase_args, icase_term } = do
  tm' <- renameTerm rep icase_term
  (_, XtorNameResult _ _ ar) <- lookupXtor icase_loc icase_name
  let args = zip ar icase_args
  pure RST.MkTermCase { tmcase_loc = icase_loc
                      , tmcase_name = icase_name
                      , tmcase_args = second Just <$> args
                      , tmcase_term = RST.termClosing args tm'
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
renameCommand (CST.PrimCmdTerm cmd) =
  renamePrimCommand cmd
renameCommand (CST.Var loc fv) =
  pure $ RST.Jump loc fv
renameCommand (CST.TermParens _loc cmd) =
  renameCommand cmd
renameCommand (CST.Apply loc tm1 tm2) = do
  tm1' <- renameTerm PrdRep tm1
  tm2' <- renameTerm CnsRep tm2
  pure $ RST.Apply loc tm1' tm2'
renameCommand (CST.Xtor loc _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Xtor")
renameCommand (CST.Semi loc _ _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Semi")
renameCommand (CST.Dtor loc _ _ _) =
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Dtor")
renameCommand (CST.Case loc _) =
  -- A "case { ... } " expression cannot be renamed into a command
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Case")
renameCommand (CST.Cocase loc _) =
  -- A "cocase { ... } " expression cannot be renamed into a command.
  throwError $ LowerError (Just loc) (CmdExpected "Command expected, but found Cocase")
renameCommand (CST.CaseOf loc tm cases) = do
  tm' <- renameTerm PrdRep tm
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cmdCases <- sequence $ renameCommandCase <$> explicitCases
      pure $ RST.CaseOfCmd loc ns tm' cmdCases
    ImplicitPrdCases implicitCases -> do
      termCasesI <- sequence $ renameTermCaseI PrdRep <$> implicitCases
      pure $ RST.CaseOfI loc PrdRep ns tm' termCasesI
    ImplicitCnsCases implicitCases -> do
      termCasesI <- sequence $ renameTermCaseI CnsRep <$> implicitCases
      pure $ RST.CaseOfI loc CnsRep ns tm' termCasesI
renameCommand (CST.CocaseOf loc tm cases) = do
  tm' <- renameTerm CnsRep tm
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Codata cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cmdCases <- sequence $ renameCommandCase <$> explicitCases
      pure $ RST.CocaseOfCmd loc ns tm' cmdCases
    ImplicitPrdCases implicitCases -> do
      termCasesI <- sequence $ renameTermCaseI PrdRep <$> implicitCases
      pure $ RST.CocaseOfI loc PrdRep ns tm' termCasesI
    ImplicitCnsCases implicitCases -> do
      termCasesI <- sequence $ renameTermCaseI CnsRep <$> implicitCases
      pure $ RST.CocaseOfI loc CnsRep ns tm' termCasesI

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
renameTerm rep    (CST.Var loc v) =
  pure $ RST.FreeVar loc rep v
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
renameTerm _ (CST.Semi _loc _xtor _subst _c) =
  error "renameTerm / Semi: not yet implemented"
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
    ImplicitPrdCases implicitCases -> do
      cases' <- sequence $ renameTermCaseI PrdRep <$> implicitCases
      pure $ RST.CocaseI loc PrdRep ns cases'
    ImplicitCnsCases implicitCases -> do
      cases' <- sequence $ renameTermCaseI CnsRep <$> implicitCases
      pure $ RST.CocaseI loc CnsRep ns cases'
renameTerm CnsRep (CST.Case loc cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence $ renameCommandCase <$> explicitCases
      pure $ RST.XCase loc CnsRep ns cases'
    ImplicitPrdCases _implicitCases -> error "not yet implemented"
    ImplicitCnsCases _implicitCases -> error "not yet implemented"
renameTerm PrdRep (CST.CaseOf loc t cases)  = do
  ns <- casesToNS cases
  intermediateCases <- analyzeCases Data cases
  case intermediateCases of
    ExplicitCases explicitCases -> do
      cases' <- sequence (renameTermCase PrdRep <$> explicitCases)
      t' <- renameTerm PrdRep t
      pure $ RST.CaseOf loc PrdRep ns t' cases'
    ImplicitPrdCases _implicitCases -> error "not yet implemented"
    ImplicitCnsCases _implicitCases -> error "not yet implemented"
renameTerm PrdRep (CST.MuAbs loc fv cmd) = do
  cmd' <- renameCommand cmd
  pure $ RST.MuAbs loc PrdRep (Just fv) (RST.commandClosing [(Cns,fv)] cmd')
renameTerm CnsRep (CST.MuAbs loc fv cmd) = do
  cmd' <- renameCommand cmd
  pure $ RST.MuAbs loc CnsRep (Just fv) (RST.commandClosing [(Prd,fv)] cmd')

renameTerm PrdRep (CST.FunApp loc fun arg) =
  renameApp loc fun arg
renameTerm CnsRep (CST.FunApp loc _fun _arg) =
  throwError (OtherError (Just loc) "Cannot rename FunApp to a consumer.")
renameTerm rep    (CST.MultiLambda loc fvs tm) =
  renameMultiLambda loc fvs tm >>= renameTerm rep
renameTerm PrdRep (CST.Lambda loc fv tm) =
  renameLambda loc fv tm
renameTerm CnsRep (CST.Lambda loc _fv _tm) =
  throwError (OtherError (Just loc) "Cannot rename Lambda to a consumer.")
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
renameTerm rep    (CST.TermParens _loc tm) =
  renameTerm rep tm
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
renameTerm rep    (CST.DtorChain pos tm dtors) =
  renameDtorChain pos tm dtors >>= renameTerm rep
renameTerm _ (CST.Apply loc _ _) =  throwError (OtherError (Just loc) "Cannot rename Command to a term.")
renameTerm _ t = throwError (OtherError (Just (CST.getLoc t)) (T.pack $ "Cannot rename "++ show t ++ " to a term."))
