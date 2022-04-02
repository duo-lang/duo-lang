module Pretty.Program where

import Data.Map qualified as M
import Prettyprinter

import Data.List (intersperse)

import Pretty.Pretty
import Pretty.Terms ()
import Pretty.Types ()
import Pretty.Common
import Syntax.AST.Types
import Syntax.AST.Terms
import Syntax.AST.Program
import Syntax.Common
import Driver.Environment

---------------------------------------------------------------------------------
-- Prettyprinting of Declarations
---------------------------------------------------------------------------------

instance PrettyAnn DataDecl where
  prettyAnn (NominalDecl ref tn dc knd xtors) =
    (case ref of
      Refined -> annKeyword "refinement" <+> mempty
      NotRefined -> mempty) <>
    prettyAnn dc <+>
    prettyAnn tn <+>
    colon <+>
    prettyAnn knd <+>
    braces (mempty <+> cat (punctuate " , " (prettyAnn <$> (fst xtors))) <+> mempty) <>
    semi

prettyAnnot :: Maybe (TypeScheme pol) -> Doc Annotation
prettyAnnot Nothing    = mempty
prettyAnnot (Just tys) = annSymbol ":" <+> prettyAnn tys

prettyPrdCnsDecl :: PrettyAnn a => PrdCnsRep pc -> IsRec -> a -> Maybe (TypeScheme pol) -> Doc Annotation -> Doc Annotation
prettyPrdCnsDecl pc Recursive fv annot ptm =
  annKeyword "def" <+> "rec" <+> prettyAnn fv <> prettyPrdCnsRep pc <+> prettyAnnot annot <+> annSymbol ":=" <+> ptm <> semi
prettyPrdCnsDecl pc NonRecursive fv annot ptm =
  annKeyword "def" <+>           prettyAnn fv <> prettyPrdCnsRep pc <+> prettyAnnot annot <+> annSymbol ":=" <+> ptm <> semi

prettyCmdDecl :: PrettyAnn a => a -> Doc Annotation -> Doc Annotation
prettyCmdDecl fv pcmd =
   annKeyword "def" <+> prettyAnn fv <+> annSymbol ":=" <+> pcmd <> semi

prettyXtorDecl :: DataCodata -> XtorName -> [(PrdCns, MonoKind)] -> EvaluationOrder -> Doc Annotation
prettyXtorDecl Data   xt args ret = annKeyword "constructor" <+> prettyAnn xt <> prettyCCList args <+> colon <+> prettyAnn ret <> semi
prettyXtorDecl Codata xt args ret = annKeyword "destructor"  <+> prettyAnn xt <> prettyCCList args <+> colon <+> prettyAnn ret <> semi

-- | Prettyprint the list of MonoKinds
prettyCCList :: [(PrdCns, MonoKind)] -> Doc Annotation
prettyCCList [] = mempty
prettyCCList ((Prd, cc):xs) = (parens   $ prettyAnn cc) <> prettyCCList xs
prettyCCList ((Cns, cc):xs) = (brackets $ prettyAnn cc) <> prettyCCList xs

prettyTyOpDecl :: TyOpName -> Associativity -> Precedence -> TypeName -> Doc Annotation
prettyTyOpDecl op assoc prec ty =
  annKeyword "type" <+> annKeyword "operator" <+>
  prettyAnn op <+> prettyAnn assoc <+> annKeyword "at" <+> prettyAnn prec <+>
  annSymbol ":=" <+> prettyAnn ty <> semi

instance PrettyAnn Declaration where
  prettyAnn (PrdCnsDecl _ _ pc isRec fv annot tm) =
    prettyPrdCnsDecl pc isRec fv annot (prettyAnn tm)
  prettyAnn (CmdDecl _ _ fv cm) =
    prettyCmdDecl fv (prettyAnn cm)
  prettyAnn (DataDecl _ _ decl) =
    prettyAnn decl
  prettyAnn (XtorDecl _ _ dc xt args ret) =
    prettyXtorDecl dc xt args ret
  prettyAnn (ImportDecl _ _ mod) =
    annKeyword "import" <+> prettyAnn mod <> semi
  prettyAnn (SetDecl _ _ txt) =
    annKeyword "set" <+> prettyAnn txt <> semi
  prettyAnn (TyOpDecl _ _ op prec assoc ty) =
    prettyTyOpDecl op assoc prec ty
    

instance PrettyAnn (NamedRep Declaration) where
  prettyAnn (NamedRep (PrdCnsDecl _ _ pc isRec fv annot tm)) =
    prettyPrdCnsDecl pc isRec fv annot (prettyAnn (openTermComplete tm))
  prettyAnn (NamedRep (CmdDecl _ _ fv cm)) =
    prettyCmdDecl fv (prettyAnn (openCommandComplete cm))
  prettyAnn (NamedRep (DataDecl _ _ decl)) =
    prettyAnn decl
  prettyAnn (NamedRep (XtorDecl _ _ dc xt args ret)) =
    prettyXtorDecl dc xt args ret
  prettyAnn (NamedRep (ImportDecl _ _ mod)) =
    annKeyword "import" <+> prettyAnn mod <> semi
  prettyAnn (NamedRep (SetDecl _ _ txt)) =
    annKeyword "set" <+> prettyAnn txt <> semi
  prettyAnn (NamedRep (TyOpDecl _ _ op prec assoc ty)) =
    prettyTyOpDecl op assoc prec ty

instance {-# OVERLAPPING #-} PrettyAnn [Declaration] where
  prettyAnn decls = vsep (prettyAnn . NamedRep <$> decls)

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

