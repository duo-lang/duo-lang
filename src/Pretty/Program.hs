module Pretty.Program where

import Data.List (intersperse)
import Data.Map qualified as M
import Prettyprinter

import TypeInference.Environment
import Pretty.Pretty
import Pretty.Terms ()
import Pretty.Types ()
import Pretty.Common
import Sugar.Desugar (Desugar(..))
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCns(..))
import Syntax.CST.Kinds
import Syntax.CST.Names
import Syntax.Core.Program qualified as Core
import Syntax.RST.Program qualified as RST
import Syntax.TST.Program qualified as TST
import Resolution.Unresolve
import Translate.EmbedTST (EmbedTST(..))
import Syntax.CST.Program (PrdCnsDeclaration(pcdecl_term))

---------------------------------------------------------------------------------
-- Data declarations
---------------------------------------------------------------------------------

instance PrettyAnn CST.DataDecl where
  prettyAnn (CST.MkDataDecl _ _ ref tn dc knd xtors) =
    (case ref of
      CST.Refined -> annKeyword "refinement" <+> mempty
      CST.NotRefined -> mempty) <>
    prettyAnn dc <+>
    prettyAnn tn <+>
    (case knd of
        Nothing -> mempty
        Just knd' ->
            colon <+>
            prettyAnn knd') <+>
    braces (mempty <+> cat (punctuate " , " (prettyAnn <$> xtors)) <+> mempty) <>
    semi

instance PrettyAnn RST.DataDecl where
  prettyAnn decl = prettyAnn (runUnresolveM (unresolve decl))

instance PrettyAnn TST.DataDecl where 
  prettyAnn decl = prettyAnn (embedTST decl)


---------------------------------------------------------------------------------
-- Producer / Consumer Declarations
---------------------------------------------------------------------------------

instance PrettyAnn CST.PrdCnsDeclaration where
  prettyAnn decl | decl.pcdecl_isRec == CST.Recursive =
    annKeyword "def" <+>
    annKeyword "rec" <+>
    prettyPrdCns decl.pcdecl_pc <+>
    prettyAnn decl.pcdecl_name <+>
    prettyAnnot decl.pcdecl_annot <+>
    annSymbol ":=" <+>
    prettyAnn decl.pcdecl_term <>
    semi
  prettyAnn decl =
    annKeyword "def" <+>
    prettyPrdCns decl.pcdecl_pc <+>
    prettyAnn decl.pcdecl_name <+>
    prettyAnnot decl.pcdecl_annot <+>
    annSymbol ":=" <+>
    prettyAnn decl.pcdecl_term <>
    semi

prettyAnnot :: Maybe CST.TypeScheme -> Doc Annotation
prettyAnnot Nothing    = mempty
prettyAnnot (Just tys) = annSymbol ":" <+> prettyAnn tys

---------------------------------------------------------------------------------
-- Command Declarations
---------------------------------------------------------------------------------

instance PrettyAnn CST.CommandDeclaration where
  prettyAnn decl =
    annKeyword "def" <+>
    annKeyword "cmd" <+>
    prettyAnn decl.cmddecl_name <+>
    annSymbol ":=" <+>
    prettyAnn decl.cmddecl_cmd <>
    semi

---------------------------------------------------------------------------------
-- Structural Xtor Declaration
---------------------------------------------------------------------------------

-- | Prettyprint the list of MonoKinds
prettyCCList :: [(PrdCns, MonoKind)] -> Doc Annotation
prettyCCList xs =  parens' comma ((\(pc,k) -> case pc of Prd -> prettyAnn k; Cns -> annKeyword "return" <+> prettyAnn k) <$> xs)

instance PrettyAnn CST.StructuralXtorDeclaration where
  prettyAnn decl =
    annKeyword (case decl.strxtordecl_xdata of CST.Data -> "constructor"; CST.Codata -> "destructor") <+>
    prettyAnn decl.strxtordecl_name <>
    prettyCCList decl.strxtordecl_arity <+>
    (case decl.strxtordecl_evalOrder of
        Nothing -> mempty
        Just strxtordecl_evalOrder' ->
            colon <+>
            prettyAnn strxtordecl_evalOrder') <>
    semi

---------------------------------------------------------------------------------
-- Import Declaration
---------------------------------------------------------------------------------

instance PrettyAnn CST.ImportDeclaration where
  prettyAnn decl =
    annKeyword "import" <+>
    prettyAnn decl.imprtdecl_module <>
    semi

---------------------------------------------------------------------------------
-- Set Declaration
---------------------------------------------------------------------------------

instance PrettyAnn CST.SetDeclaration where
  prettyAnn decl =
    annKeyword "set" <+>
    prettyAnn decl.setdecl_option <>
    semi

---------------------------------------------------------------------------------
-- Type Operator Declaration
---------------------------------------------------------------------------------

instance PrettyAnn CST.TyOpDeclaration where
  prettyAnn decl =
    annKeyword "type" <+>
    annKeyword "operator" <+>
    prettyAnn decl.tyopdecl_sym <+>
    prettyAnn decl.tyopdecl_assoc <+>
    annKeyword "at" <+>
    prettyAnn decl.tyopdecl_prec <+>
    annSymbol ":=" <+>
    prettyAnn decl.tyopdecl_res <>
    semi

---------------------------------------------------------------------------------
-- Type Synonym Declaration
---------------------------------------------------------------------------------

instance PrettyAnn CST.TySynDeclaration where
  prettyAnn decl =
    annKeyword "type" <+>
    prettyAnn decl.tysyndecl_name <+>
    annSymbol ":=" <+>
    prettyAnn decl.tysyndecl_res <>
    semi

---------------------------------------------------------------------------------
-- Class Declaration
---------------------------------------------------------------------------------

-- | Prettyprint list of type variables for class declaration.
prettyTVars :: [(Variance, SkolemTVar, MonoKind)] -> Doc Annotation
prettyTVars tvs = parens $ cat (punctuate comma (prettyTParam <$> tvs))

instance PrettyAnn CST.ClassDeclaration where
  prettyAnn decl =
    annKeyword "class" <+>
    prettyAnn decl.classdecl_name <+>
    prettyTVars decl.classdecl_kinds.kindArgs <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> decl.classdecl_methods))))) <>
    semi

---------------------------------------------------------------------------------
-- Instance Declaration
---------------------------------------------------------------------------------

instance PrettyAnn CST.InstanceDeclaration where
  prettyAnn decl =
    annKeyword "instance" <+>
    prettyAnn decl.instancedecl_name <+> annSymbol ":" <+>
    prettyAnn decl.instancedecl_class <+>
    prettyAnn decl.instancedecl_typ <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> decl.instancedecl_cases))))) <>
    semi

---------------------------------------------------------------------------------
-- Declaration
---------------------------------------------------------------------------------

instance PrettyAnn Core.Declaration where
  prettyAnn decl = prettyAnn (embedCore decl)

instance PrettyAnn TST.Declaration where
  prettyAnn decl = prettyAnn (embedTST decl)

instance PrettyAnn RST.Declaration where
  prettyAnn decl = prettyAnn (runUnresolveM (unresolve decl))

    
instance PrettyAnn CST.Declaration where
  prettyAnn (CST.PrdCnsDecl decl) = prettyAnn decl
  prettyAnn (CST.CmdDecl decl) = prettyAnn decl
  prettyAnn (CST.DataDecl decl) = prettyAnn decl
  prettyAnn (CST.XtorDecl decl) = prettyAnn decl
  prettyAnn (CST.ImportDecl decl) = prettyAnn decl
  prettyAnn (CST.SetDecl decl) = prettyAnn decl
  prettyAnn (CST.TyOpDecl decl) = prettyAnn decl
  prettyAnn (CST.TySynDecl decl) = prettyAnn decl
  prettyAnn (CST.ClassDecl decl) = prettyAnn decl
  prettyAnn (CST.InstanceDecl decl) = prettyAnn decl  
  prettyAnn CST.ParseErrorDecl = "<PARSE ERROR: SHOULD NOT OCCUR>"

---------------------------------------------------------------------------------
-- Program
---------------------------------------------------------------------------------

instance PrettyAnn CST.Module where
  prettyAnn mod = vsep (moduleDecl : (prettyAnn <$> mod.mod_decls))
    where moduleDecl = annKeyword "module" <+> prettyAnn mod.mod_name <> semi

instance PrettyAnn TST.Module where
  prettyAnn mod = vsep (moduleDecl : (prettyAnn <$> mod.mod_decls))
    where moduleDecl = annKeyword "module" <+> prettyAnn mod.mod_name <> semi

---------------------------------------------------------------------------------
-- Prettyprinting of Environments
---------------------------------------------------------------------------------

instance PrettyAnn Environment where
  prettyAnn env =
    vsep [ppPrds,ppCns,ppCmds, ppDecls ]
    where
      ppPrds = case M.toList env.prdEnv of
        [] -> mempty
        env -> vsep $ intersperse "" $ ("Producers:" : ( (\(v,(_,_,ty)) -> prettyAnn v <+> ":" <+> prettyAnn ty) <$> env)) ++ [""]
      ppCns  = case M.toList env.cnsEnv of
        [] -> mempty
        env -> vsep $ intersperse "" $ ("Consumers:" : ( (\(v,(_,_,ty)) -> prettyAnn v <+> ":" <+> prettyAnn ty) <$> env)) ++ [""]
      ppCmds = case M.toList env.cmdEnv of
        [] -> mempty
        env -> vsep $ intersperse "" $ ("Commands" : ( (\(v,_) -> prettyAnn v) <$> env)) ++ [""]
      ppDecls = case env.declEnv of
        [] -> mempty
        env -> vsep $ intersperse "" $ ("Type declarations:" : (prettyAnn . snd <$> env)) ++ [""]

