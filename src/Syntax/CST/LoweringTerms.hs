module Syntax.CST.LoweringTerms where

import Syntax.CST.Terms qualified as CST
import Syntax.Terms qualified as AST
import Syntax.CommonTerm

lowerTerm :: PrdCnsRep pc -> CST.Term -> AST.Term pc Parsed
lowerTerm = undefined

lowerCommand :: CST.Command -> AST.Command Parsed
lowerCommand = undefined