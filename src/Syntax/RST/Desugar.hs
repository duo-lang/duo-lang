module Syntax.RST.Desugar where 
import Syntax.Common
import Utils
import Syntax.RST.Terms

resVar :: FreeVarName
resVar = MkFreeVarName "$result"

caseD :: Loc -> NominalStructural -> Term Prd -> [TermCase Prd] -> Term Prd
caseD loc ns tm cases = MuAbs loc PrdRep Nothing $ commandClosing [(Cns, resVar)] (shiftCmd cmd)
  where
    f :: TermCase Prd -> CmdCase
    f (MkTermCase loc xtor args t) = MkCmdCase loc xtor args (Apply loc t (FreeVar loc CnsRep resVar))
    cmd = Apply loc tm (XMatch loc CnsRep ns (map f cases))
    