module Xfunc.Xfunc (transformable, xFuncDataDecl, xFuncXtors) where


import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.CST.Names qualified as CST
import Syntax.CST.Program qualified as CST
--import Syntax.RST.Program qualified as RST
import Syntax.RST.Kinds qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.RST.Names qualified as RST
import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Types qualified as TST
import qualified Syntax.RST.Names as TST
import Data.Set qualified as Set
--import Data.List qualified as List
import Data.Text as Text ( Text, append, head, tail, singleton )
import Data.Char as Char ( toUpper, toLower )
import Data.Either as Either
import Translate.EmbedTST ( embedTST )
import Sugar.Desugar (embedCore)
import Resolution.Unresolve (unresolve, runUnresolveM)
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
-- helper functions
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

liftPrdCns :: TST.PrdCnsDeclaration pc -> CST.PrdCnsDeclaration
liftPrdCns decl = runUnresolveM (unresolve (embedCore (embedTST decl)))

liftDataDecl :: TST.DataDecl -> CST.DataDecl
liftDataDecl decl = runUnresolveM (unresolve (embedTST decl))

------------------------------------------------------------------------------
-- transforming producers/consumers to constructors/destructors
------------------------------------------------------------------------------


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


xFuncXtors :: TST.Module -> TST.DataDecl -> XfuncM [CST.PrdCnsDeclaration]
xFuncXtors mod decl@(TST.NominalDecl _ _ _ CST.Codata _ _) = pure $ createPrdCns (liftPrdCns <$> getPrdCns (filterDeclsTST CST.PrdRep mod.mod_decls) decl.data_name) (liftDataDecl decl)
xFuncXtors mod decl@(TST.NominalDecl _ _ _ CST.Data _ _) = pure $ createPrdCns (liftPrdCns <$> getPrdCns (filterDeclsTST CST.CnsRep mod.mod_decls) decl.data_name) (liftDataDecl decl) 
xFuncXtors _ (TST.RefinementDecl loc _ _ _ _ _ _ _ _) = throwXfuncError (XfuncError loc "Cannot xfunc refinement data declaration")


createPrdCns :: [CST.PrdCnsDeclaration] -> CST.DataDecl -> [CST.PrdCnsDeclaration]
createPrdCns pcdecls (CST.MkDataDecl _ _ _ _ CST.Data _ sigs) = constructPrdDecl  pcdecls <$> sigs 
createPrdCns pcdecls (CST.MkDataDecl _ _ _ _ CST.Codata _ sigs) = constructCnsDecl pcdecls <$> sigs


filterTermCase :: CST.XtorName -> [CST.TermCase] -> XfuncM CST.Term
filterTermCase xtor ((CST.MkTermCase _ (CST.PatXtor _ xtorname _) term):rest) = if xtor == xtorname then pure term else filterTermCase xtor rest 
filterTermCase _ _ = throwXfuncError (XfuncError Loc.defaultLoc "no xtor matched")

createTermCase :: CST.XtorName -> CST.PrdCnsDeclaration -> XfuncM CST.TermCase
createTermCase xtor (CST.MkPrdCnsDeclaration _ _ _ _ name _ (CST.Case loc list)) = do
  term <- filterTermCase xtor list
  pure $ CST.MkTermCase loc (CST.PatXtor loc (CST.MkXtorName (capFirstLetter (name.unFreeVarName))) []) term
createTermCase _ _ = throwXfuncError (XfuncError Loc.defaultLoc "xtor error")


createTermCaseList :: CST.XtorName -> [CST.PrdCnsDeclaration] -> [XfuncM CST.TermCase]
createTermCaseList xtor (pcdecl:rest) =  createTermCase xtor pcdecl : createTermCaseList xtor rest
createTermCaseList _ [] = []

constructPrdDecl :: [CST.PrdCnsDeclaration] -> CST.XtorSig -> CST.PrdCnsDeclaration
constructPrdDecl pcdecls (CST.MkXtorSig xtor _) = CST.MkPrdCnsDeclaration {
    loc = Loc.defaultLoc
  , doc = Nothing
  , prd_cns = CST.Prd
  , isRecursive = CST.NonRecursive
  , name = CST.MkFreeVarName (lowerFirstLetter (xtor.unXtorName))
  , annot = Nothing
  , term = CST.Cocase Loc.defaultLoc (Either.rights (createTermCaseList xtor pcdecls))
}

constructCnsDecl :: [CST.PrdCnsDeclaration] -> CST.XtorSig -> CST.PrdCnsDeclaration
constructCnsDecl pcdecls (CST.MkXtorSig xtor _) = CST.MkPrdCnsDeclaration {
    loc = Loc.defaultLoc
  , doc = Nothing
  , prd_cns = CST.Cns
  , isRecursive = CST.NonRecursive
  , name = CST.MkFreeVarName (lowerFirstLetter (xtor.unXtorName))
  , annot = Nothing
  , term = CST.Case Loc.defaultLoc (Either.rights (createTermCaseList xtor pcdecls))
}
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