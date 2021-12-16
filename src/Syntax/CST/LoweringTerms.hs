module Syntax.CST.LoweringTerms where

import Syntax.CST.Terms qualified as CST
import Syntax.Terms qualified as AST
import Syntax.CommonTerm
import Utils

lowerSubstitution :: CST.Substitution -> AST.Substitution Parsed
lowerSubstitution = fmap lowerPrdCnsTerm

lowerPrdCnsTerm :: CST.PrdCnsTerm -> AST.PrdCnsTerm Parsed
lowerPrdCnsTerm (CST.PrdTerm tm) = AST.PrdTerm (lowerTerm PrdRep tm)
lowerPrdCnsTerm (CST.CnsTerm tm) = AST.CnsTerm (lowerTerm CnsRep tm)

lowerTerm :: PrdCnsRep pc -> CST.Term -> AST.Term pc Parsed
lowerTerm rep    (CST.Var loc v)               = AST.FreeVar loc rep v
lowerTerm rep    (CST.XtorCall loc xtor subst) = AST.XtorCall loc rep xtor (lowerSubstitution subst)
lowerTerm rep    (CST.XMatch loc cases)        = undefined
lowerTerm rep    (CST.MuAbs loc fv cmd)        = undefined
lowerTerm rep    (CST.Dtor loc tor tm subst)   = undefined
lowerTerm rep    (CST.Match loc tm cases)      = undefined
lowerTerm rep    (CST.Comatch loc cases)       = undefined
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
