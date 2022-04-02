module Renamer.Terms (lowerTerm, lowerCommand) where

import Control.Monad.Except (throwError)
import Data.Bifunctor ( second )
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map qualified as M
import Text.Megaparsec.Pos (SourcePos)

import Errors
import Renamer.Definition
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Terms qualified as CST
import Syntax.Common
import Utils

---------------------------------------------------------------------------------
-- Check Arity of Xtor
---------------------------------------------------------------------------------

checkXtorArity :: Loc -> (XtorName, DataCodata) -> Arity -> RenamerM ()
checkXtorArity loc (xt, dc) arityUsed = do
  (_,aritySpecified) <- lookupXtor loc (xt, dc)
  if arityUsed /= aritySpecified
    then throwError (LowerError (Just loc) (XtorArityMismatch xt aritySpecified arityUsed))
    else pure ()


---------------------------------------------------------------------------------
-- Check Arity of Xtor
---------------------------------------------------------------------------------

lowerSubstitution :: CST.Substitution -> RenamerM RST.Substitution
lowerSubstitution [] = pure []
lowerSubstitution (CST.PrdTerm tm:tms) = do
  tm' <- lowerTerm PrdRep tm
  subst <- lowerSubstitution tms
  pure (RST.PrdTerm tm':subst)
lowerSubstitution (CST.CnsTerm tm:tms) = do
  tm' <- lowerTerm CnsRep tm
  subst <- lowerSubstitution tms
  pure (RST.CnsTerm tm':subst)


lowerSubstitutionI :: CST.SubstitutionI -> RenamerM (RST.SubstitutionI Prd)
lowerSubstitutionI (subst1, _, subst2) = do
  subst1' <- lowerSubstitution subst1
  subst2' <- lowerSubstitution subst2
  pure (subst1', PrdRep, subst2')



lowerTermCase :: DataCodata -> CST.TermCase -> RenamerM RST.TermCase
lowerTermCase dc (loc, xtor, bs, tm) = do
  tm' <- lowerTerm PrdRep tm
  checkXtorArity loc (xtor, dc) (fst <$> bs)
  pure RST.MkTermCase { tmcase_ext = loc
                      , tmcase_name = xtor
                      , tmcase_args = second Just <$> bs
                      , tmcase_term = RST.termClosing bs tm'
                      }

termCasesToNS :: [CST.TermCase] -> DataCodata -> RenamerM NominalStructural
termCasesToNS [] _ = pure Structural
termCasesToNS ((loc,xtor,_,_):_) dc = fst <$> lookupXtor loc (xtor, dc)

lowerTermCaseI :: DataCodata -> CST.TermCaseI -> RenamerM RST.TermCaseI
lowerTermCaseI dc (loc, xtor, (bs1,(),bs2), tm) = do
  tm' <- lowerTerm PrdRep tm
  checkXtorArity loc (xtor,dc) ((fst <$> bs1) ++ [Cns] ++ (fst <$> bs2))
  pure RST.MkTermCaseI { tmcasei_ext = loc
                       , tmcasei_name = xtor
                       , tmcasei_args = (second Just <$> bs1, (), second Just <$> bs2)
                       -- HACK: We want to ensure that the implicit argument gets the intuitive De-Bruijn index.
                       -- termClosing doesn't support implicit arguments yet. We can emulate it for now by passing
                       -- a string that cannot be parsed as a variable (e.g. *).
                       , tmcasei_term = RST.termClosing (bs1 ++ [(Cns, MkFreeVarName "*")] ++ bs2) tm'
                       }

termCasesIToNS :: [CST.TermCaseI] -> DataCodata -> RenamerM NominalStructural
termCasesIToNS [] _ = pure Structural
termCasesIToNS ((loc,xtor,_,_):_) dc = fst <$> lookupXtor loc (xtor, dc)

lowerCommandCase :: DataCodata -> CST.CommandCase -> RenamerM RST.CmdCase
lowerCommandCase dc (loc, xtor, bs, cmd) = do
  cmd' <- lowerCommand cmd
  checkXtorArity loc (xtor,dc) (fst <$> bs)
  pure RST.MkCmdCase { cmdcase_ext = loc
                     , cmdcase_name = xtor
                     , cmdcase_args = second Just <$> bs
                     , cmdcase_cmd = RST.commandClosing bs cmd'
                     }

-- TODO: Check that all command cases use the same nominal/structural variant.
commandCasesToNS :: [CST.CommandCase] -> DataCodata -> RenamerM NominalStructural
commandCasesToNS [] _ = pure Structural
commandCasesToNS ((loc,xtor,_,_):_) dc = fst <$> lookupXtor loc (xtor, dc)

lowerTerm :: PrdCnsRep pc -> CST.Term -> RenamerM (RST.Term pc)
lowerTerm rep    (CST.Var loc v)               =
  pure $ RST.FreeVar loc rep Nothing v
lowerTerm PrdRep (CST.Xtor loc xtor subst)     = do
  (ns, _) <- lookupXtor loc (xtor, Data)
  checkXtorArity loc (xtor,Data) (CST.substitutionToArity subst)
  RST.Xtor loc PrdRep Nothing ns xtor <$> lowerSubstitution subst
lowerTerm CnsRep (CST.Xtor loc xtor subst)     = do
  (ns, _) <- lookupXtor loc (xtor, Codata)
  checkXtorArity loc (xtor,Codata) (CST.substitutionToArity subst)
  RST.Xtor loc CnsRep Nothing ns xtor <$> lowerSubstitution subst
lowerTerm CnsRep (CST.XMatch loc Data cases)        = do
  cases' <- sequence (lowerCommandCase Data <$> cases)
  ns <- commandCasesToNS cases Data
  pure $ RST.XMatch loc CnsRep Nothing ns cases'
lowerTerm PrdRep (CST.XMatch loc Data _)       = throwError (OtherError (Just loc) "Cannot lower pattern match to a producer.")
lowerTerm PrdRep (CST.XMatch loc Codata cases)        = do
  cases' <- sequence (lowerCommandCase Codata <$> cases)
  ns <- commandCasesToNS cases Codata
  pure $ RST.XMatch loc PrdRep Nothing ns cases'
lowerTerm CnsRep (CST.XMatch loc Codata _)     = throwError (OtherError (Just loc) "Cannot lower copattern match to a consumer.")
lowerTerm PrdRep (CST.MuAbs loc fv cmd)        = do
  cmd' <- lowerCommand cmd
  pure $ RST.MuAbs loc PrdRep Nothing (Just fv) (RST.commandClosing [(Cns,fv)] cmd')
lowerTerm CnsRep (CST.MuAbs loc fv cmd)        = do
  cmd' <- lowerCommand cmd
  pure $ RST.MuAbs loc CnsRep Nothing (Just fv) (RST.commandClosing [(Prd,fv)] cmd')
lowerTerm PrdRep (CST.Dtor loc xtor tm subst)  = do
  (ns, _) <- lookupXtor loc (xtor, Codata)
  checkXtorArity loc (xtor,Codata) (CST.substitutionIToArity subst)
  tm' <- lowerTerm PrdRep tm
  subst' <- lowerSubstitutionI subst
  pure $ RST.Dtor loc PrdRep Nothing ns xtor tm' subst'
lowerTerm CnsRep (CST.Dtor loc _xtor _tm _s)   = throwError (OtherError (Just loc) "Cannot lower Dtor to a consumer (TODO).")
lowerTerm PrdRep (CST.Case loc tm cases)       = do
  cases' <- sequence (lowerTermCase Data <$> cases)
  tm' <- lowerTerm PrdRep tm
  ns <- termCasesToNS cases Data
  pure $ RST.Case loc Nothing ns tm' cases'
lowerTerm CnsRep (CST.Case loc _tm _cases)     = throwError (OtherError (Just loc) "Cannot lower Match to a consumer (TODO)")
lowerTerm PrdRep (CST.Cocase loc cases)        = do
  cases' <- sequence (lowerTermCaseI Codata <$> cases)
  ns <- termCasesIToNS cases Codata
  pure $ RST.Cocase loc Nothing ns cases'
lowerTerm CnsRep (CST.Cocase loc _cases)       = throwError (OtherError (Just loc) "Cannot lower Comatch to a consumer (TODO)")
lowerTerm PrdRep (CST.NatLit loc ns i)         = lowerNatLit loc ns i
lowerTerm CnsRep (CST.NatLit loc _ns _i)       = throwError (OtherError (Just loc) "Cannot lower NatLit to a consumer.")
lowerTerm rep    (CST.TermParens _loc tm)      = lowerTerm rep tm
lowerTerm rep    (CST.DtorChain pos tm dtors)  = lowerDtorChain pos tm dtors >>= lowerTerm rep
lowerTerm PrdRep (CST.FunApp loc fun arg)      = lowerApp loc fun arg
lowerTerm CnsRep (CST.FunApp loc _fun _arg)    = throwError (OtherError (Just loc) "Cannot lower FunApp to a consumer.")
lowerTerm rep    (CST.MultiLambda loc fvs tm)  = lowerMultiLambda loc fvs tm >>= lowerTerm rep
lowerTerm PrdRep (CST.Lambda loc fv tm)        = lowerLambda loc fv tm
lowerTerm CnsRep (CST.Lambda loc _fv _tm)      = throwError (OtherError (Just loc) "Cannot lower Lambda to a consumer.")
lowerTerm PrdRep (CST.PrimLitI64 loc i)        = pure $ RST.PrimLitI64 loc i
lowerTerm CnsRep (CST.PrimLitI64 loc _)        = throwError (OtherError (Just loc) "Cannot lower primitive literal to a consumer.")
lowerTerm PrdRep (CST.PrimLitF64 loc d)        = pure $ RST.PrimLitF64 loc d
lowerTerm CnsRep (CST.PrimLitF64 loc _)        = throwError (OtherError (Just loc) "Cannot lower primitive literal to a consumer.")



lowerDtorChain :: SourcePos -> CST.Term -> NonEmpty (XtorName, CST.SubstitutionI, SourcePos) -> RenamerM CST.Term
lowerDtorChain startPos tm ((xtor, subst, endPos) :| [])   = pure $ CST.Dtor (Loc startPos endPos) xtor tm subst
lowerDtorChain startPos tm ((xtor, subst, endPos) :| (x:xs)) = lowerDtorChain startPos (CST.Dtor (Loc startPos endPos) xtor tm subst) (x :| xs)


-- | Lower a multi-lambda abstraction
lowerMultiLambda :: Loc -> [FreeVarName] -> CST.Term -> RenamerM (CST.Term)
lowerMultiLambda _ [] tm = pure tm
lowerMultiLambda loc (fv:fvs) tm = CST.Lambda loc fv <$> lowerMultiLambda loc fvs tm

-- | Lower a lambda abstraction.
lowerLambda :: Loc -> FreeVarName -> CST.Term -> RenamerM (RST.Term Prd)
lowerLambda loc var tm = do
  tm' <- lowerTerm PrdRep tm
  pure $ RST.Cocase loc Nothing Nominal [ RST.MkTermCaseI loc (MkXtorName "Ap")
                                                      ([(Prd, Just var)], (), [])
                                                      (RST.termClosing [(Prd, var)] tm')
                                ]

-- | Lower a natural number literal.
lowerNatLit :: Loc -> NominalStructural -> Int -> RenamerM (RST.Term Prd)
lowerNatLit loc ns 0 = pure $ RST.Xtor loc PrdRep Nothing ns (MkXtorName "Z") []
lowerNatLit loc ns n = do
  n' <- lowerNatLit loc ns (n-1)
  pure $ RST.Xtor loc PrdRep Nothing ns (MkXtorName "S") [RST.PrdTerm n']

-- | Lower an application.
lowerApp :: Loc -> CST.Term -> CST.Term -> RenamerM (RST.Term Prd)
lowerApp loc fun arg = do
  fun' <- lowerTerm PrdRep fun
  arg' <- lowerTerm PrdRep arg
  pure $ RST.Dtor loc PrdRep Nothing Nominal (MkXtorName "Ap") fun' ([RST.PrdTerm arg'],PrdRep,[])

lowerCommand :: CST.Command -> RenamerM RST.Command
lowerCommand (CST.Apply loc tm1 tm2)       = RST.Apply loc Nothing <$> lowerTerm PrdRep tm1 <*> lowerTerm CnsRep tm2
lowerCommand (CST.Print loc tm cmd)        = RST.Print loc <$> lowerTerm PrdRep tm <*> lowerCommand cmd
lowerCommand (CST.Read loc tm)             = RST.Read loc <$> lowerTerm CnsRep tm
lowerCommand (CST.Jump loc fv)             = pure $ RST.Jump loc fv
lowerCommand (CST.ExitSuccess loc)         = pure $ RST.ExitSuccess loc
lowerCommand (CST.ExitFailure loc)         = pure $ RST.ExitFailure loc
lowerCommand (CST.CommandParens _loc cmd)  = lowerCommand cmd
lowerCommand (CST.PrimOp loc pt op subst)  = do
  let arity = CST.substitutionToArity subst
  _ <- checkPrimOpArity loc (pt, op) arity
  RST.PrimOp loc pt op <$> lowerSubstitution subst

---------------------------------------------------------------------------------
-- Check Arity of PrimOp
---------------------------------------------------------------------------------

checkPrimOpArity :: Loc -> (PrimitiveType, PrimitiveOp) -> Arity -> RenamerM ()
checkPrimOpArity loc primOp arityUsed = do
  case M.lookup primOp primOps of
    Nothing -> throwError (LowerError (Just loc) (UndefinedPrimOp primOp))
    Just aritySpecified ->
      if arityUsed /= aritySpecified then
        throwError (LowerError (Just loc) (PrimOpArityMismatch primOp aritySpecified arityUsed))
      else
        pure ()
