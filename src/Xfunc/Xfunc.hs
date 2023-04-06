module Xfunc.Xfunc (transformable, xFuncDataDecl) where



import Syntax.CST.Types qualified as CST
import Syntax.CST.Names qualified as CST
import Syntax.RST.Kinds qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Types qualified as TST
import qualified Syntax.RST.Names as TST
import Data.Set qualified as Set


----------------------------
-- determine the new xtors
----------------------------

-- get all prd or cns 
-- 

flipDC :: CST.DataCodata -> CST.DataCodata
flipDC CST.Data = CST.Codata 
flipDC CST.Codata = CST.Data 

-- filters for Prd or Cns Declarations
filterDecls ::  CST.PrdCnsRep pc -> [TST.Declaration] -> [TST.PrdCnsDeclaration pc]
filterDecls CST.PrdRep ((TST.PrdCnsDecl CST.PrdRep decl):rest)  = decl : filterDecls CST.PrdRep rest
filterDecls CST.CnsRep ((TST.PrdCnsDecl CST.CnsRep decl):rest)  = decl : filterDecls CST.CnsRep rest
filterDecls pc (_:rest) = filterDecls pc rest
filterDecls _ [] = []


-- filters for PrdCnsDeclarations that (co-)pattern match on the given (co-)data type
getPrdCns :: [TST.PrdCnsDeclaration pc] -> TST.RnTypeName -> [TST.PrdCnsDeclaration pc]
getPrdCns (decl@(TST.MkPrdCnsDeclaration _ _ _ _ _ _ (TST.XCase _ _ _ _ (RST.Nominal typename) _ )):rest) dataname = if typename == dataname.rnTnName then decl : getPrdCns rest dataname else getPrdCns rest dataname
getPrdCns _ _ = []


getNewXtors :: TST.PrdCnsDeclaration pc -> TST.XtorSig RST.Pos
getNewXtors (TST.MkPrdCnsDeclaration _ _ CST.PrdRep _ name (TST.Annotated (TST.TypeScheme _ _ typ)) _) = TST.MkXtorSig (CST.MkXtorName name.unFreeVarName) [TST.PrdCnsType CST.PrdRep typ]
getNewXtors (TST.MkPrdCnsDeclaration _ _ CST.PrdRep _ name (TST.Inferred (TST.TypeScheme _ _ typ)) _) = TST.MkXtorSig (CST.MkXtorName name.unFreeVarName) [TST.PrdCnsType CST.PrdRep typ]
getNewXtors (TST.MkPrdCnsDeclaration _ _ CST.CnsRep _ name (TST.Annotated (TST.TypeScheme _ _ typ)) _) = TST.MkXtorSig (CST.MkXtorName name.unFreeVarName) [TST.PrdCnsType CST.CnsRep typ]
getNewXtors (TST.MkPrdCnsDeclaration _ _ CST.CnsRep _ name (TST.Inferred (TST.TypeScheme _ _ typ)) _) = TST.MkXtorSig (CST.MkXtorName name.unFreeVarName) [TST.PrdCnsType CST.CnsRep typ]



constructNewDataDecl :: [TST.PrdCnsDeclaration pc] -> TST.DataDecl -> TST.DataDecl
constructNewDataDecl prdcns oldDecl@(TST.NominalDecl _ _ _ CST.Codata _ _) = TST.NominalDecl {  data_loc = oldDecl.data_loc,
                                                                                                data_doc = oldDecl.data_doc,
                                                                                                data_name = oldDecl.data_name,
                                                                                                data_polarity = flipDC oldDecl.data_polarity,
                                                                                                data_kind = oldDecl.data_kind,
                                                                                                data_xtors = (getNewXtors <$> prdcns , [])          
}
constructNewDataDecl prdcns oldDecl@(TST.NominalDecl _ _ _ CST.Data _ _) = TST.NominalDecl {  data_loc = oldDecl.data_loc,
                                                                                                data_doc = oldDecl.data_doc,
                                                                                                data_name = oldDecl.data_name,
                                                                                                data_polarity = flipDC oldDecl.data_polarity,
                                                                                                data_kind = oldDecl.data_kind,
                                                                                                data_xtors = (getNewXtors <$> prdcns, [])           
}
constructNewDataDecl _ _ = undefined


xFuncDataDecl :: TST.Module -> TST.DataDecl -> TST.DataDecl
xFuncDataDecl mod decl@(TST.NominalDecl _ _ _ CST.Codata _ _) = constructNewDataDecl (getPrdCns (filterDecls CST.PrdRep mod.mod_decls) decl.data_name) decl
xFuncDataDecl mod decl@(TST.NominalDecl _ _ _ CST.Data _ _) = constructNewDataDecl (getPrdCns (filterDecls CST.CnsRep mod.mod_decls) decl.data_name) decl
xFuncDataDecl _ _ = undefined

---------------------------

-- check if a DataDecl has parameters
transformable :: TST.DataDecl -> Bool
transformable decl = Set.size (RST.allTypeVars (decl.data_kind)) == 0

-- xfunc a (co)datatype in a module
-- xfunc :: TST.Module -> TST.DataDecl -> TST.Module
-- xfunc = undefined