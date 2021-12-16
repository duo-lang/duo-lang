module Syntax.CST.LoweringTerms where

import Data.Bifunctor ( second )

import Syntax.CST.Terms qualified as CST
import Syntax.Terms qualified as AST
import Syntax.CommonTerm
import Utils

lowerSubstitution :: CST.Substitution -> AST.Substitution Parsed
lowerSubstitution = fmap lowerPrdCnsTerm

lowerSubstitutionI :: CST.SubstitutionI -> AST.SubstitutionI Parsed Prd
lowerSubstitutionI (subst1, _, subst2) = (lowerSubstitution subst1, PrdRep, lowerSubstitution subst2)

lowerPrdCnsTerm :: CST.PrdCnsTerm -> AST.PrdCnsTerm Parsed
lowerPrdCnsTerm (CST.PrdTerm tm) = AST.PrdTerm (lowerTerm PrdRep tm)
lowerPrdCnsTerm (CST.CnsTerm tm) = AST.CnsTerm (lowerTerm CnsRep tm)

lowerTermCase :: CST.TermCase -> AST.TermCase Parsed
lowerTermCase (loc, xtor, bs, tm) = AST.MkTermCase { tmcase_ext = loc
                                                   , tmcase_name = xtor
                                                   , tmcase_args = second Just <$> bs
                                                   , tmcase_term = AST.termClosing bs (lowerTerm PrdRep tm)
                                                   }

lowerTermCaseI :: CST.TermCaseI -> AST.TermCaseI Parsed
lowerTermCaseI (loc, xtor, (bs1,(),bs2), tm) = AST.MkTermCaseI { tmcasei_ext = loc
                                                               , tmcasei_name = xtor
                                                               , tmcasei_args = (second Just <$> bs1, (), second Just <$> bs2)
                                                               -- HACK: We want to ensure that the implicit argument gets the intuitive De-Bruijn index.
                                                               -- termClosing doesn't support implicit arguments yet. We can emulate it for now by passing
                                                               -- a string that cannot be parsed as a variable (e.g. *).
                                                               , tmcasei_term = AST.termClosing (bs1 ++ [(Cns, "*")] ++ bs2) (lowerTerm PrdRep tm)
                                                               }



lowerCommandCase :: CST.CommandCase -> AST.CmdCase Parsed
lowerCommandCase (loc, xtor, bs, cmd) = AST.MkCmdCase { cmdcase_ext = loc
                                                      , cmdcase_name = xtor
                                                      , cmdcase_args = second Just <$> bs
                                                      , cmdcase_cmd = AST.commandClosing bs (lowerCommand cmd)
                                                      }

lowerTerm :: PrdCnsRep pc -> CST.Term -> AST.Term pc Parsed
lowerTerm rep    (CST.Var loc v)               = AST.FreeVar loc rep v
lowerTerm rep    (CST.XtorCall loc xtor subst) = AST.XtorCall loc rep xtor (lowerSubstitution subst)
lowerTerm rep    (CST.XMatch loc cases)        = AST.XMatch loc rep undefined (lowerCommandCase <$> cases)
lowerTerm PrdRep (CST.MuAbs loc fv cmd)        = AST.MuAbs loc PrdRep (Just fv) (AST.commandClosing [(Cns,fv)] (lowerCommand cmd))
lowerTerm CnsRep (CST.MuAbs loc fv cmd)        = AST.MuAbs loc CnsRep (Just fv) (AST.commandClosing [(Prd,fv)] (lowerCommand cmd))
lowerTerm PrdRep (CST.Dtor loc xtor tm subst)  = AST.Dtor loc xtor (lowerTerm PrdRep tm) (lowerSubstitutionI subst)
lowerTerm CnsRep (CST.Dtor _loc _xtor _tm _s)  = error "Cannot lower Dtor to a consumer (TODO)."
lowerTerm PrdRep (CST.Match loc tm cases)      = AST.Match loc undefined (lowerTerm PrdRep tm) (lowerTermCase <$> cases)
lowerTerm CnsRep (CST.Match _loc _tm _cases)   = error "Cannot lower Match to a consumer (TODO)"
lowerTerm PrdRep (CST.Comatch loc cases)       = AST.Comatch loc undefined (lowerTermCaseI <$> cases)
lowerTerm CnsRep (CST.Comatch _loc _cases)     = error "Cannot lower Comatch to a consumer (TODO)"
lowerTerm PrdRep (CST.NatLit loc ns i)         = lowerNatLit loc ns i
lowerTerm CnsRep (CST.NatLit _loc _ns _i)      = error "Cannot lower NatLit to a consumer."
lowerTerm rep    (CST.TermParens _loc tm)      = lowerTerm rep tm
lowerTerm PrdRep (CST.FunApp loc fun arg)      = lowerApp loc fun arg
lowerTerm CnsRep (CST.FunApp _loc _fun _arg)   = error "Cannot lower FunApp to a consumer."
lowerTerm PrdRep (CST.Lambda loc fv tm)        = lowerLambda loc fv tm
lowerTerm CnsRep (CST.Lambda _loc _fv _tm)     = error "Cannot lower Lambda to a consumer."

-- | Lower a lambda abstraction.
lowerLambda :: Loc -> FreeVarName -> CST.Term -> AST.Term Prd Parsed
lowerLambda loc var tm = AST.Comatch loc Structural
  [
    AST.MkTermCaseI loc (MkXtorName Structural "Ap")
                        ([(Prd, Just var)], (), [])
                        (AST.termClosing [(Prd, var)] (lowerTerm PrdRep tm))
  ]

-- | Lower a natural number literal.
lowerNatLit :: Loc -> NominalStructural -> Int -> AST.Term Prd Parsed
lowerNatLit loc ns 0 = AST.XtorCall loc PrdRep (MkXtorName ns "Z") []
lowerNatLit loc ns n = AST.XtorCall loc PrdRep (MkXtorName ns "S") [AST.PrdTerm $ lowerNatLit loc ns (n-1)]

-- | Lower an application.
lowerApp :: Loc -> CST.Term -> CST.Term -> AST.Term Prd Parsed
lowerApp loc fun arg = AST.Dtor loc (MkXtorName Structural "Ap") (lowerTerm PrdRep fun) ([AST.PrdTerm (lowerTerm PrdRep arg)],PrdRep,[])

lowerCommand :: CST.Command -> AST.Command Parsed
lowerCommand (CST.Apply loc tm1 tm2)      = AST.Apply loc Nothing (lowerTerm PrdRep tm1) (lowerTerm CnsRep tm2)
lowerCommand (CST.Print loc tm cmd)       = AST.Print loc (lowerTerm PrdRep tm) (lowerCommand cmd)
lowerCommand (CST.Read loc tm)            = AST.Read loc (lowerTerm CnsRep tm)
lowerCommand (CST.Call loc fv)            = AST.Call loc fv
lowerCommand (CST.Done loc)               = AST.Done loc
lowerCommand (CST.CommandParens _loc cmd) = lowerCommand cmd
