module Sugar.AST
  where

import Syntax.AST.Terms
import Syntax.Common
import Utils
import Syntax.Common.Annot

{-
pattern CaseOfCmd :: Loc -> NominalStructural -> Term Prd -> [CmdCase] -> Command
pattern CaseOfCmd loc ns t cases <- Apply loc ApplyAnnotCaseOfCmd Nothing t (XCase _ MatchAnnotCaseOfCmd CnsRep ns cases)
 where
    CaseOfCmd loc ns t cases = Apply loc ApplyAnnotCaseOfCmd Nothing t (XCase loc MatchAnnotCaseOfCmd CnsRep ns cases)
-}