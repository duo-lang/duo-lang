module Xfunc.Xfunc (transformable, getNewXtors) where

import Syntax.CST.Types qualified as CST
import Syntax.CST.Names qualified as CST
import Syntax.RST.Kinds qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.RST.Names qualified as RST
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Data.Set qualified as Set


----------------------------
-- determine the new xtors
----------------------------

-- check a pattern match if it matches on a given data type
checkPatternMatch :: CST.TypeName -> TST.PrdCnsDeclaration CST.Prd -> Bool
checkPatternMatch tn (TST.MkPrdCnsDeclaration _ _ _ _ _ _ (TST.XCase _ _ _ _ (RST.Nominal typename) _ )) = tn == typename
checkPatternMatch _ _ = False 

getTypeNames :: TST.PrdCnsDeclaration CST.Prd -> CST.TypeName
getTypeNames (TST.MkPrdCnsDeclaration _ _ _ _ _ _ (TST.XCase _ _ _ _ (RST.Nominal typename) _ )) = typename
getTypeNames _ = CST.MkTypeName "error"

filterDecls ::  CST.PrdCnsRep pc -> [TST.Declaration] -> [TST.PrdCnsDeclaration pc]
filterDecls CST.PrdRep ((TST.PrdCnsDecl CST.PrdRep decl):rest)  = decl : filterDecls CST.PrdRep rest
filterDecls CST.CnsRep ((TST.PrdCnsDecl CST.CnsRep decl):rest)  = decl : filterDecls CST.CnsRep rest
filterDecls pc (_:rest) = filterDecls pc rest
filterDecls _ [] = []

declToName :: TST.PrdCnsDeclaration CST.Prd -> CST.FreeVarName
declToName (TST.MkPrdCnsDeclaration _ _ _ _ name _ _) = name 

declsToNames :: [TST.PrdCnsDeclaration CST.Prd] -> [CST.TypeName]
declsToNames = map getTypeNames

getNewXtorsTemp :: TST.DataDecl -> [TST.Declaration] -> [TST.PrdCnsDeclaration CST.Prd]
getNewXtorsTemp datadecl decls = [d | d <- filterDecls CST.PrdRep decls, checkPatternMatch datadecl.data_name.rnTnName d ]

getNewXtors :: TST.Module -> TST.DataDecl -> [CST.TypeName]
getNewXtors mod decl = declsToNames(filterDecls CST.PrdRep mod.mod_decls) 

---------------------------

-- check if a DataDecl has parameters
transformable :: TST.DataDecl -> Bool
transformable decl = Set.size (RST.allTypeVars (decl.data_kind)) == 0

-- xfunc a (co)datatype in a module
xfunc :: TST.Module -> TST.DataDecl -> TST.Module
xfunc = undefined