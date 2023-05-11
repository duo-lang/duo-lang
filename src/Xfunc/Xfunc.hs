module Xfunc.Xfunc (transformable, xFuncDataDecl) where



import Syntax.CST.Types qualified as CST
import Syntax.CST.Names qualified as CST
import Syntax.CST.Program qualified as CST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Kinds qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.RST.Names qualified as RST
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Types qualified as TST
import qualified Syntax.RST.Names as TST
import Data.Set qualified as Set
import Data.Text as Text ( Text, append, head, tail, singleton )
import Data.Char as Char ( toUpper, toLower )
import Translate.EmbedTST ( embedTST )
import Sugar.Desugar (embedCore)
import Loc ( Loc , defaultLoc)

------------------------------------------------------------------------------
-- TODO
------------------------------------------------------------------------------
-- > introduce arguments to xtors when available
-- > transform a whole module, at the moment there is no opportunity to get the range of a whole module
-- > 
------------------------------------------------------------------------------
------------------------------------------------------------------------------


------------------------------------------------------------------------------
-- error handling
------------------------------------------------------------------------------

data XfuncError 
    = XfuncError Loc Text
    deriving Show


type XfuncM a = Either XfuncError a

throwXfuncError :: forall a. XfuncError -> XfuncM a
throwXfuncError = Left

------------------------------------------------------------------------------
-- transforming producers/consumers to constructors/destructors
------------------------------------------------------------------------------

-- helper for capitalizing names
capFirstLetter :: Text -> Text
capFirstLetter "" = ""
capFirstLetter text = append (singleton (Char.toUpper (Text.head text))) (Text.tail text)

-- helper for lowering names
lowerFirstLetter :: Text -> Text
lowerFirstLetter "" = ""
lowerFirstLetter text = append (singleton (Char.toLower (Text.head text))) (Text.tail text)

-- flips the constructors of CST.DataCodata
flipDC :: CST.DataCodata -> CST.DataCodata
flipDC CST.Data = CST.Codata 
flipDC CST.Codata = CST.Data 

-- filters a list of declarations for producer declarations XOR consumer declarations
-- here it is used to filter [TST.Declaration] in a module
filterDeclsTST ::  CST.PrdCnsRep pc -> [TST.Declaration] -> [TST.PrdCnsDeclaration pc]
filterDeclsTST CST.PrdRep ((TST.PrdCnsDecl CST.PrdRep decl):rest)  = decl : filterDeclsTST CST.PrdRep rest
filterDeclsTST CST.CnsRep ((TST.PrdCnsDecl CST.CnsRep decl):rest)  = decl : filterDeclsTST CST.CnsRep rest
filterDeclsTST pc (_:rest) = filterDeclsTST pc rest
filterDeclsTST _ [] = []


-- filters [TST.PrdCnsDeclaration pc] for a given type name the declarations pattern match on
-- for now the type it pattern matches on is used, later that can just be the type of TST.PrdCnsDeclaration
getPrdCns :: [TST.PrdCnsDeclaration pc] -> TST.RnTypeName -> [TST.PrdCnsDeclaration pc]
getPrdCns (decl@(TST.MkPrdCnsDeclaration _ _ _ _ _ _ (TST.XCase _ _ _ _ (RST.Nominal typename) _ )):rest) dataname = if typename == dataname.rnTnName then decl : getPrdCns rest dataname else getPrdCns rest dataname
getPrdCns _ _ = []


-- creates a Xtor out of a TST.PrdCnsDeclaration
-- the new Xtor won't have any arguments since a PrdCnsDeclaration can't have arguments yet
getNewXtors :: TST.PrdCnsDeclaration pc -> TST.XtorSig RST.Pos
getNewXtors (TST.MkPrdCnsDeclaration _ _ CST.PrdRep _ name _ _) = TST.MkXtorSig (CST.MkXtorName (capFirstLetter name.unFreeVarName)) []
getNewXtors (TST.MkPrdCnsDeclaration _ _ CST.CnsRep _ name _ _) = TST.MkXtorSig (CST.MkXtorName (capFirstLetter name.unFreeVarName)) []


-- constructs a data declaration out of a codata declaration and its producers
-- constructs a codata declaration out of a data declaration and its consumers
constructNewDataDecl :: [TST.PrdCnsDeclaration pc] -> TST.DataDecl -> XfuncM TST.DataDecl
constructNewDataDecl prdcns oldDecl@(TST.NominalDecl _ _ _ CST.Codata _ _) = pure $ TST.NominalDecl {  data_loc = oldDecl.data_loc,
                                                                                                data_doc = oldDecl.data_doc,
                                                                                                data_name = oldDecl.data_name,
                                                                                                data_polarity = flipDC oldDecl.data_polarity,
                                                                                                data_kind = oldDecl.data_kind,
                                                                                                data_xtors = (getNewXtors <$> prdcns , [])          
}
constructNewDataDecl prdcns oldDecl@(TST.NominalDecl _ _ _ CST.Data _ _) = pure $ TST.NominalDecl {  data_loc = oldDecl.data_loc,
                                                                                                data_doc = oldDecl.data_doc,
                                                                                                data_name = oldDecl.data_name,
                                                                                                data_polarity = flipDC oldDecl.data_polarity,
                                                                                                data_kind = oldDecl.data_kind,
                                                                                                data_xtors = (getNewXtors <$> prdcns, [])           
}
constructNewDataDecl _ (TST.RefinementDecl loc _ _ _ _ _ _ _ _) = throwXfuncError (XfuncError loc "Cannot xfunc refinement data declaration")

-- xfunc a data declaration in a module
xFuncDataDecl :: TST.Module -> TST.DataDecl -> XfuncM TST.DataDecl
xFuncDataDecl mod decl@(TST.NominalDecl _ _ _ CST.Codata _ _) = constructNewDataDecl (getPrdCns (filterDeclsTST CST.PrdRep mod.mod_decls) decl.data_name) decl
xFuncDataDecl mod decl@(TST.NominalDecl _ _ _ CST.Data _ _) = constructNewDataDecl (getPrdCns (filterDeclsTST CST.CnsRep mod.mod_decls) decl.data_name) decl
xFuncDataDecl _ (TST.RefinementDecl loc _ _ _ _ _ _ _ _) = throwXfuncError (XfuncError loc "Cannot xfunc refinement data declaration")

------------------------------------------------------------------------------
-- transforming constructors/destructors to producers/consumers
-- WORK IN PROGRESS: this part includes some attempts that might not work
------------------------------------------------------------------------------
-- lifting module to RST
-- collect terms
-- create prd/cns

liftModule :: TST.Module -> RST.Module
liftModule mod = embedCore (embedTST mod)


filterModule :: TST.Module -> TST.DataDecl -> XfuncM TST.Module
filterModule mod datadecl@(TST.NominalDecl _ _ _ CST.Codata _ _) = pure $ TST.MkModule { mod_name = mod.mod_name,
                                                                                  mod_libpath = mod.mod_libpath,
                                                                                  mod_decls = TST.DataDecl datadecl : (TST.PrdCnsDecl CST.PrdRep <$> getPrdCns (filterDeclsTST CST.PrdRep mod.mod_decls) datadecl.data_name)}
filterModule mod datadecl@(TST.NominalDecl _ _ _ CST.Data _ _) = pure $ TST.MkModule { mod_name = mod.mod_name,
                                                                                  mod_libpath = mod.mod_libpath,
                                                                                  mod_decls = TST.DataDecl datadecl : (TST.PrdCnsDecl CST.CnsRep <$> getPrdCns (filterDeclsTST CST.CnsRep mod.mod_decls) datadecl.data_name)}
filterModule _ (TST.RefinementDecl loc _ _ _ _ _ _ _ _) = throwXfuncError (XfuncError loc "Cannot xfunc refinement data declaration")


filterDeclsRST ::  CST.PrdCnsRep pc -> [RST.Declaration] -> [RST.PrdCnsDeclaration pc]
filterDeclsRST CST.PrdRep ((RST.PrdCnsDecl CST.PrdRep decl):rest)  = decl : filterDeclsRST CST.PrdRep rest
filterDeclsRST CST.CnsRep ((RST.PrdCnsDecl CST.CnsRep decl):rest)  = decl : filterDeclsRST CST.CnsRep rest
filterDeclsRST pc (_:rest) = filterDeclsRST pc rest
filterDeclsRST _ [] = []

getCmdCase :: CST.XtorName -> RST.CmdCase -> RST.Command
getCmdCase name (RST.MkCmdCase loc (RST.XtorPat _ xtor _) cmd) = undefined

getTermCase :: CST.XtorName -> RST.TermCase pc-> RST.Term pc
getTermCase name (RST.MkTermCase loc (RST.XtorPat _ xtor _) tm) = undefined

getTermCaseI :: CST.XtorName -> RST.TermCaseI pc -> RST.Term pc
getTermCaseI name (RST.MkTermCaseI loc (RST.XtorPatI _ xtor _) tm) = undefined

getTerm :: CST.XtorName -> RST.PrdCnsDeclaration pc -> (CST.XtorName, Either [RST.Term pc] [RST.Command])
getTerm xtor (RST.MkPrdCnsDeclaration loc doc pcdecl isRec fvname annot term) = 
    case term of
        RST.XCase _ _ _ cases  -> (xtor, Right (getCmdCase xtor <$> cases))
        RST.CaseOf _ _ _ _ cases -> (xtor, Left (getTermCase xtor <$> cases))
        RST.CocaseOf _ _ _ _ cases -> (xtor, Left (getTermCase xtor <$> cases))
        RST.CaseI _ _ _ cases -> undefined 
        RST.CocaseI _ _ _ cases -> undefined
        _ -> undefined

createTermCns :: RST.Term CST.Cns
createTermCns = undefined

createTermPrd :: RST.Term CST.Prd
createTermPrd = undefined

constructCnsDecl :: RST.DataDecl -> XfuncM (RST.PrdCnsDeclaration CST.Cns)
constructCnsDecl datadecl@(RST.NominalDecl _ _ name CST.Codata _ _) = pure $ RST.MkPrdCnsDeclaration{ pcdecl_loc = Loc.defaultLoc,
                                                                                      pcdecl_doc = datadecl.data_doc,
                                                                                      pcdecl_pc = CST.CnsRep,
                                                                                      pcdecl_isRec = CST.NonRecursive,
                                                                                      pcdecl_name = CST.MkFreeVarName (lowerFirstLetter (name.rnTnName.unTypeName)) ,
                                                                                      pcdecl_annot = Nothing,
                                                                                      pcdecl_term = createTermCns}
constructCnsDecl (RST.NominalDecl loc _ _ _ _ _)  = throwXfuncError (XfuncError loc "should not occur")
constructCnsDecl (RST.RefinementDecl loc _ _ _ _ _)  = throwXfuncError (XfuncError loc "Cannot xfunc refinement data declaration")   

constructPrdDecl :: RST.DataDecl -> XfuncM (RST.PrdCnsDeclaration CST.Prd)                                                                                   
constructPrdDecl datadecl@(RST.NominalDecl _ _ name CST.Data _ _) = pure $ RST.MkPrdCnsDeclaration{ pcdecl_loc = Loc.defaultLoc,
                                                                                      pcdecl_doc = datadecl.data_doc,
                                                                                      pcdecl_pc = CST.PrdRep,
                                                                                      pcdecl_isRec = CST.NonRecursive,
                                                                                      pcdecl_name = CST.MkFreeVarName (lowerFirstLetter (name.rnTnName.unTypeName)) ,
                                                                                      pcdecl_annot = Nothing,
                                                                                      pcdecl_term = createTermPrd}   
constructPrdDecl (RST.NominalDecl loc _ _ _ _ _)  = throwXfuncError (XfuncError loc "should not occur")
constructPrdDecl (RST.RefinementDecl loc _ _ _ _ _ ) = throwXfuncError (XfuncError loc "Cannot xfunc refinement data declaration")                                                                                                                                                                       


------------------------------------------------------------------------------
-- transformability checks
------------------------------------------------------------------------------

-- check if a DataDecl has parameters
hasParameters :: TST.DataDecl -> Bool
hasParameters decl = Set.size (RST.allTypeVars (decl.data_kind)) == 0

-- check if transformation can be executed
-- can be extended like shown with other tests
transformable :: TST.DataDecl -> Bool
transformable decl = hasParameters decl && True


-- xfunc a (co)datatype in a module
-- xfunc :: TST.Module -> TST.DataDecl -> TST.Module
-- xfunc = undefined