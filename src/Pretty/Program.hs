module Pretty.Program where

import Data.Map qualified as M
import Prettyprinter

import Data.List (intersperse)

import Pretty.Pretty
import Pretty.Terms ()
import Pretty.Types ()
import Pretty.Common
import Syntax.CST.Program qualified as CST
import Syntax.Common.TypesUnpol qualified as Unpol
import Syntax.Common.TypesPol qualified as Pol
import Syntax.RST.Program qualified as RST
import Syntax.TST.Program qualified as TST
import Syntax.Core.Program qualified as Core
import Syntax.Common
import Driver.Environment
import Translate.Embed
import Translate.Reparse
import Syntax.CST.Program (PrdCnsDeclaration(pcdecl_term))

---------------------------------------------------------------------------------
-- Data declarations
---------------------------------------------------------------------------------

instance PrettyAnn Unpol.DataDecl where
  prettyAnn (Unpol.NominalDecl ref tn dc knd xtors) =
    (case ref of
      Refined -> annKeyword "refinement" <+> mempty
      NotRefined -> mempty) <>
    prettyAnn dc <+>
    prettyAnn tn <+>
    colon <+>
    prettyAnn knd <+>
    braces (mempty <+> cat (punctuate " , " (prettyAnn <$> xtors)) <+> mempty) <>
    semi

instance PrettyAnn Pol.DataDecl where
  prettyAnn decl = prettyAnn (embedTyDecl decl)

---------------------------------------------------------------------------------
-- Producer / Consumer Declarations
---------------------------------------------------------------------------------

instance PrettyAnn CST.PrdCnsDeclaration where
  prettyAnn CST.MkPrdCnsDeclaration { pcdecl_pc, pcdecl_isRec = Recursive, pcdecl_name, pcdecl_annot, pcdecl_term} =
    annKeyword "def" <+>
    annKeyword "rec" <+>
    prettyPrdCns pcdecl_pc <+>
    prettyAnn pcdecl_name <+>
    prettyAnnot pcdecl_annot <+>
    annSymbol ":=" <+>
    prettyAnn pcdecl_term <>
    semi
  prettyAnn CST.MkPrdCnsDeclaration { pcdecl_pc, pcdecl_isRec = NonRecursive, pcdecl_name, pcdecl_annot, pcdecl_term} =
    annKeyword "def" <+>
    prettyPrdCns pcdecl_pc <+>
    prettyAnn pcdecl_name <+>
    prettyAnnot pcdecl_annot <+>
    annSymbol ":=" <+>
    prettyAnn pcdecl_term <>
    semi

prettyAnnot :: Maybe Unpol.TypeScheme -> Doc Annotation
prettyAnnot Nothing    = mempty
prettyAnnot (Just tys) = annSymbol ":" <+> prettyAnn tys

---------------------------------------------------------------------------------
-- Command Declarations
---------------------------------------------------------------------------------

instance PrettyAnn CST.CommandDeclaration where
  prettyAnn CST.MkCommandDeclaration { cmddecl_name, cmddecl_cmd } =
    annKeyword "def" <+>
    annKeyword "cmd" <+>
    prettyAnn cmddecl_name <+>
    annSymbol ":=" <+>
    prettyAnn cmddecl_cmd <>
    semi

---------------------------------------------------------------------------------
-- Other
---------------------------------------------------------------------------------

prettyCmdDecl :: PrettyAnn a => a -> Doc Annotation -> Doc Annotation
prettyCmdDecl fv pcmd =
   annKeyword "def" <+> "cmd" <+> prettyAnn fv <+> annSymbol ":=" <+> pcmd <> semi

prettyXtorDecl :: DataCodata -> XtorName -> [(PrdCns, MonoKind)] -> Maybe EvaluationOrder -> Doc Annotation
prettyXtorDecl Data   xt args ret = annKeyword "constructor" <+> prettyAnn xt <> prettyCCList args <+> colon <+> prettyAnn ret <> semi
prettyXtorDecl Codata xt args ret = annKeyword "destructor"  <+> prettyAnn xt <> prettyCCList args <+> colon <+> prettyAnn ret <> semi

-- | Prettyprint the list of MonoKinds
prettyCCList :: [(PrdCns, MonoKind)] -> Doc Annotation
prettyCCList xs =  parens' comma ((\(pc,k) -> case pc of Prd -> prettyAnn k; Cns -> annKeyword "return" <+> prettyAnn k) <$> xs)

prettyTyOpDecl :: TyOpName -> Associativity -> Precedence -> TypeName -> Doc Annotation
prettyTyOpDecl op assoc prec ty =
  annKeyword "type" <+> annKeyword "operator" <+>
  prettyAnn op <+> prettyAnn assoc <+> annKeyword "at" <+> prettyAnn prec <+>
  annSymbol ":=" <+> prettyAnn ty <> semi

instance PrettyAnn Core.Declaration where
  prettyAnn decl = prettyAnn (embedCoreDecl decl)

instance PrettyAnn TST.Declaration where
  prettyAnn decl = prettyAnn (embedTSTDecl decl)

instance PrettyAnn RST.Declaration where
  prettyAnn decl = prettyAnn (reparseDecl decl)

    
instance PrettyAnn CST.Declaration where
  prettyAnn (CST.PrdCnsDecl decl) = prettyAnn decl
  prettyAnn (CST.CmdDecl decl) = prettyAnn decl
  prettyAnn (CST.DataDecl _ _ decl) =
    prettyAnn decl
  prettyAnn (CST.XtorDecl _ _ dc xt args ret) =
    prettyXtorDecl dc xt args ret
  prettyAnn (CST.ImportDecl _ _ mod) =
    annKeyword "import" <+> prettyAnn mod <> semi
  prettyAnn (CST.SetDecl _ _ txt) =
    annKeyword "set" <+> prettyAnn txt <> semi
  prettyAnn (CST.TyOpDecl _ _ op prec assoc ty) =
    prettyTyOpDecl op assoc prec ty
  prettyAnn (CST.TySynDecl _ _ nm ty) =
    annKeyword "type" <+> prettyAnn nm <+> annSymbol ":=" <+> prettyAnn ty <> semi
  prettyAnn CST.ParseErrorDecl =
    undefined

instance {-# OVERLAPPING #-} PrettyAnn [TST.Declaration] where
  prettyAnn decls = vsep (prettyAnn <$> decls)

instance {-# OVERLAPPING #-} PrettyAnn [CST.Declaration] where
  prettyAnn decls = vsep (prettyAnn <$> decls)

---------------------------------------------------------------------------------
-- Prettyprinting of Environments
---------------------------------------------------------------------------------

instance PrettyAnn Environment where
  prettyAnn MkEnvironment { prdEnv, cnsEnv, cmdEnv, declEnv } =
    vsep [ppPrds,ppCns,ppCmds, ppDecls ]
    where
      ppPrds = case M.toList prdEnv of
        [] -> mempty
        env -> vsep $ intersperse "" $ ("Producers:" : ( (\(v,(_,_,ty)) -> prettyAnn v <+> ":" <+> prettyAnn ty) <$> env)) ++ [""]
      ppCns  = case M.toList cnsEnv of
        [] -> mempty
        env -> vsep $ intersperse "" $ ("Consumers:" : ( (\(v,(_,_,ty)) -> prettyAnn v <+> ":" <+> prettyAnn ty) <$> env)) ++ [""]
      ppCmds = case M.toList cmdEnv of
        [] -> mempty
        env -> vsep $ intersperse "" $ ("Commands" : ( (\(v,_) -> prettyAnn v) <$> env)) ++ [""]
      ppDecls = case declEnv of
        [] -> mempty
        env -> vsep $ intersperse "" $ ("Type declarations:" : (prettyAnn . snd <$> env)) ++ [""]

