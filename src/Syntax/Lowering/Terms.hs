module Syntax.Lowering.Terms (lowerTerm, lowerCommand) where

import Control.Monad.Except (throwError)
import Data.Bifunctor ( second )
import Data.List.NonEmpty (NonEmpty(..))
import Text.Megaparsec.Pos (SourcePos)

import Errors
import Syntax.Lowering.Lowering
import Syntax.CST.Terms qualified as CST
import Syntax.AST.Terms qualified as AST
import Syntax.CommonTerm
import Utils

lowerSubstitution :: CST.Substitution -> LowerM (AST.Substitution Parsed)
lowerSubstitution subst = sequence $ fmap lowerPrdCnsTerm subst

lowerSubstitutionI :: CST.SubstitutionI -> LowerM (AST.SubstitutionI Parsed Prd)
lowerSubstitutionI (subst1, _, subst2) = do
  subst1' <- lowerSubstitution subst1
  subst2' <- lowerSubstitution subst2
  pure (subst1', PrdRep, subst2')

lowerPrdCnsTerm :: CST.PrdCnsTerm -> LowerM (AST.PrdCnsTerm Parsed)
lowerPrdCnsTerm (CST.PrdTerm tm) = AST.PrdTerm <$> lowerTerm PrdRep tm
lowerPrdCnsTerm (CST.CnsTerm tm) = AST.CnsTerm <$> lowerTerm CnsRep tm

lowerTermCase :: CST.TermCase -> LowerM (AST.TermCase Parsed)
lowerTermCase (loc, xtor, bs, tm) = do
  tm' <- lowerTerm PrdRep tm
  pure AST.MkTermCase { tmcase_ext = loc
                      , tmcase_name = xtor
                      , tmcase_args = second Just <$> bs
                      , tmcase_term = AST.termClosing bs tm'
                      }

termCasesToNS :: [CST.TermCase] -> NominalStructural
termCasesToNS [] = Structural
termCasesToNS ((_,xtor,_,_):_) = xtorNominalStructural xtor

lowerTermCaseI :: CST.TermCaseI -> LowerM (AST.TermCaseI Parsed)
lowerTermCaseI (loc, xtor, (bs1,(),bs2), tm) = do
  tm' <- lowerTerm PrdRep tm
  pure AST.MkTermCaseI { tmcasei_ext = loc
                       , tmcasei_name = xtor
                       , tmcasei_args = (second Just <$> bs1, (), second Just <$> bs2)
                       -- HACK: We want to ensure that the implicit argument gets the intuitive De-Bruijn index.
                       -- termClosing doesn't support implicit arguments yet. We can emulate it for now by passing
                       -- a string that cannot be parsed as a variable (e.g. *).
                       , tmcasei_term = AST.termClosing (bs1 ++ [(Cns, "*")] ++ bs2) tm'
                       }

termCasesIToNS :: [CST.TermCaseI] -> NominalStructural
termCasesIToNS [] = Structural
termCasesIToNS ((_,xtor,_,_):_) = xtorNominalStructural xtor

lowerCommandCase :: CST.CommandCase -> LowerM (AST.CmdCase Parsed)
lowerCommandCase (loc, xtor, bs, cmd) = do
  cmd' <- lowerCommand cmd
  pure AST.MkCmdCase { cmdcase_ext = loc
                     , cmdcase_name = xtor
                     , cmdcase_args = second Just <$> bs
                     , cmdcase_cmd = AST.commandClosing bs cmd'
                     }

-- TODO: Check that all command cases use the same nominal/structural variant.
commandCasesToNS :: [CST.CommandCase] -> NominalStructural
commandCasesToNS [] = Structural
commandCasesToNS ((_,xtor,_,_):_) = xtorNominalStructural xtor

lowerTerm :: PrdCnsRep pc -> CST.Term -> LowerM (AST.Term pc Parsed)
lowerTerm rep    (CST.Var loc v)               = pure $ AST.FreeVar loc rep v
lowerTerm rep    (CST.Xtor loc xtor subst)     = AST.Xtor loc rep xtor <$> lowerSubstitution subst
lowerTerm rep    (CST.XMatch loc cases)        = do
  cases' <- sequence (lowerCommandCase <$> cases)
  pure $ AST.XMatch loc rep (commandCasesToNS cases) cases'
lowerTerm PrdRep (CST.MuAbs loc fv cmd)        = do
  cmd' <- lowerCommand cmd
  pure $ AST.MuAbs loc PrdRep (Just fv) (AST.commandClosing [(Cns,fv)] cmd')
lowerTerm CnsRep (CST.MuAbs loc fv cmd)        = do
  cmd' <- lowerCommand cmd
  pure $ AST.MuAbs loc CnsRep (Just fv) (AST.commandClosing [(Prd,fv)] cmd')
lowerTerm PrdRep (CST.Dtor loc xtor tm subst)  = AST.Dtor loc xtor <$> lowerTerm PrdRep tm <*> lowerSubstitutionI subst
lowerTerm CnsRep (CST.Dtor _loc _xtor _tm _s)  = throwError (OtherError Nothing "Cannot lower Dtor to a consumer (TODO).")
lowerTerm PrdRep (CST.Case loc tm cases)       = do
  cases' <- sequence (lowerTermCase <$> cases)
  tm' <- lowerTerm PrdRep tm
  pure $ AST.Case loc (termCasesToNS cases) tm' cases'
lowerTerm CnsRep (CST.Case _loc _tm _cases)    = throwError (OtherError Nothing "Cannot lower Match to a consumer (TODO)")
lowerTerm PrdRep (CST.Cocase loc cases)        = do
  cases' <- sequence (lowerTermCaseI <$> cases)
  pure $ AST.Cocase loc (termCasesIToNS cases) cases'
lowerTerm CnsRep (CST.Cocase _loc _cases)      = throwError (OtherError Nothing "Cannot lower Comatch to a consumer (TODO)")
lowerTerm PrdRep (CST.NatLit loc ns i)         = lowerNatLit loc ns i
lowerTerm CnsRep (CST.NatLit _loc _ns _i)      = throwError (OtherError Nothing "Cannot lower NatLit to a consumer.")
lowerTerm rep    (CST.TermParens _loc tm)      = lowerTerm rep tm
lowerTerm rep    (CST.DtorChain pos tm dtors)  = lowerDtorChain pos tm dtors >>= lowerTerm rep
lowerTerm PrdRep (CST.FunApp loc fun arg)      = lowerApp loc fun arg
lowerTerm CnsRep (CST.FunApp _loc _fun _arg)   = throwError (OtherError Nothing "Cannot lower FunApp to a consumer.")
lowerTerm rep    (CST.MultiLambda loc fvs tm)  = lowerMultiLambda loc fvs tm >>= lowerTerm rep
lowerTerm PrdRep (CST.Lambda loc fv tm)        = lowerLambda loc fv tm
lowerTerm CnsRep (CST.Lambda _loc _fv _tm)     = throwError (OtherError Nothing "Cannot lower Lambda to a consumer.")


lowerDtorChain :: SourcePos -> CST.Term -> NonEmpty (XtorName, CST.SubstitutionI, SourcePos) -> LowerM CST.Term
lowerDtorChain startPos tm ((xtor, subst, endPos) :| [])   = pure $ CST.Dtor (Loc startPos endPos) xtor tm subst
lowerDtorChain startPos tm ((xtor, subst, endPos) :| (x:xs)) = lowerDtorChain startPos (CST.Dtor (Loc startPos endPos) xtor tm subst) (x :| xs)


-- | Lower a multi-lambda abstraction
lowerMultiLambda :: Loc -> [FreeVarName] -> CST.Term -> LowerM (CST.Term)
lowerMultiLambda _ [] tm = pure tm
lowerMultiLambda loc (fv:fvs) tm = CST.Lambda loc fv <$> lowerMultiLambda loc fvs tm

-- | Lower a lambda abstraction.
lowerLambda :: Loc -> FreeVarName -> CST.Term -> LowerM (AST.Term Prd Parsed)
lowerLambda loc var tm = do
  tm' <- lowerTerm PrdRep tm
  pure $ AST.Cocase loc Structural [ AST.MkTermCaseI loc (MkXtorName Structural "Ap")
                                                         ([(Prd, Just var)], (), [])
                                                        (AST.termClosing [(Prd, var)] tm')
                                   ]

-- | Lower a natural number literal.
lowerNatLit :: Loc -> NominalStructural -> Int -> LowerM (AST.Term Prd Parsed)
lowerNatLit loc ns 0 = pure $ AST.Xtor loc PrdRep (MkXtorName ns "Z") []
lowerNatLit loc ns n = do
  n' <- lowerNatLit loc ns (n-1)
  pure $ AST.Xtor loc PrdRep (MkXtorName ns "S") [AST.PrdTerm n']

-- | Lower an application.
lowerApp :: Loc -> CST.Term -> CST.Term -> LowerM (AST.Term Prd Parsed)
lowerApp loc fun arg = do
  fun' <- lowerTerm PrdRep fun
  arg' <- lowerTerm PrdRep arg
  pure $ AST.Dtor loc (MkXtorName Structural "Ap") fun' ([AST.PrdTerm arg'],PrdRep,[])

lowerCommand :: CST.Command -> LowerM (AST.Command Parsed)
lowerCommand (CST.Apply loc tm1 tm2)      = AST.Apply loc Nothing <$> lowerTerm PrdRep tm1 <*> lowerTerm CnsRep tm2
lowerCommand (CST.Print loc tm cmd)       = AST.Print loc <$> lowerTerm PrdRep tm <*> lowerCommand cmd
lowerCommand (CST.Read loc tm)            = AST.Read loc <$> lowerTerm CnsRep tm
lowerCommand (CST.Call loc fv)            = pure $ AST.Call loc fv
lowerCommand (CST.Done loc)               = pure $ AST.Done loc
lowerCommand (CST.CommandParens _loc cmd) = lowerCommand cmd
