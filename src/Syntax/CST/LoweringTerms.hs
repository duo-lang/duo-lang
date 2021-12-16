module Syntax.CST.LoweringTerms where

import Syntax.CST.Terms qualified as CST
import Syntax.Terms qualified as AST
import Syntax.CommonTerm

lowerTerm :: PrdCnsRep pc -> CST.Term -> AST.Term pc Parsed
lowerTerm = undefined

lowerCommand :: CST.Command -> AST.Command Parsed
lowerCommand (CST.Apply loc tm1 tm2) = AST.Apply loc Nothing (lowerTerm PrdRep tm1) (lowerTerm CnsRep tm2)
lowerCommand (CST.Print loc tm cmd) = AST.Print loc (lowerTerm PrdRep tm) (lowerCommand cmd)
lowerCommand (CST.Read loc tm) = AST.Read loc (lowerTerm CnsRep tm)
lowerCommand (CST.Call loc fv) = AST.Call loc fv
lowerCommand (CST.Done loc) = AST.Done loc
lowerCommand (CST.CommandParens _loc cmd) = lowerCommand cmd
