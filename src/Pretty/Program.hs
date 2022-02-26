module Pretty.Program where

import Data.Map qualified as M
import Prettyprinter

import Data.List (intersperse)

import Pretty.Pretty
import Pretty.Terms ()
import Pretty.Types ()
import Syntax.CST.Program (IsRec(..))
import Syntax.AST.Program
import Syntax.AST.Types
import Syntax.AST.Terms
import Syntax.CommonTerm

---------------------------------------------------------------------------------
-- Prettyprinting of Declarations
---------------------------------------------------------------------------------

instance PrettyAnn DataCodata where
  prettyAnn Data = annKeyword "data"
  prettyAnn Codata = annKeyword "codata"

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

instance PrettyAnn ModuleName where
  prettyAnn (ModuleName nm) = prettyAnn nm

instance PrettyAnn (PrdCnsRep pc) where
  prettyAnn PrdRep = annKeyword "prd"
  prettyAnn CnsRep = annKeyword "cns"

prettyAnnot :: Maybe (TypeScheme pol) -> Doc Annotation
prettyAnnot Nothing    = mempty
prettyAnnot (Just tys) = annSymbol ":" <+> prettyAnn tys

prettyPrdCnsDecl :: Pretty a => PrdCnsRep pc -> IsRec -> a -> Maybe (TypeScheme pol) -> Doc Annotation -> Doc Annotation
prettyPrdCnsDecl pc Recursive fv annot ptm =
  prettyAnn pc <+> "rec" <+> pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> ptm <> semi
prettyPrdCnsDecl pc NonRecursive fv annot ptm =
  prettyAnn pc <+>           pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> ptm <> semi

prettyCmdDecl :: Pretty a => a -> Doc Annotation -> Doc Annotation
prettyCmdDecl fv pcmd =
   annKeyword "cmd" <+> pretty fv <+> annSymbol ":=" <+> pcmd <> semi


instance PrettyAnn (Declaration ext) where
  prettyAnn (PrdCnsDecl _ pc isRec fv annot tm) =
    prettyPrdCnsDecl pc isRec fv annot (prettyAnn tm)
  prettyAnn (CmdDecl _ fv cm) =
    prettyCmdDecl fv (prettyAnn cm)
  prettyAnn (DataDecl _ decl) =
    prettyAnn decl
  prettyAnn (ImportDecl _ mod) =
    annKeyword "import" <+> prettyAnn mod <> semi
  prettyAnn (SetDecl _ txt) =
    annKeyword "set" <+> prettyAnn txt <> semi

instance PrettyAnn (NamedRep (Declaration ext)) where
  prettyAnn (NamedRep (PrdCnsDecl _ pc isRec fv annot tm)) =
    prettyPrdCnsDecl pc isRec fv annot (prettyAnn (openTermComplete tm))
  prettyAnn (NamedRep (CmdDecl _ fv cm)) =
    prettyCmdDecl fv (prettyAnn (openCommandComplete cm))
  prettyAnn (NamedRep (DataDecl _ decl)) =
    prettyAnn decl
  prettyAnn (NamedRep (ImportDecl _ mod)) =
    annKeyword "import" <+> prettyAnn mod <> semi
  prettyAnn (NamedRep (SetDecl _ txt)) =
    annKeyword "set" <+> prettyAnn txt <> semi

instance {-# OVERLAPPING #-} PrettyAnn [Declaration Parsed] where
  prettyAnn decls = vsep (prettyAnn . NamedRep <$> decls)

instance {-# OVERLAPPING #-} PrettyAnn [Declaration Inferred] where
  prettyAnn decls = vsep (prettyAnn . NamedRep <$> decls)

---------------------------------------------------------------------------------
-- Prettyprinting of Environments
---------------------------------------------------------------------------------

instance PrettyAnn (Environment ph) where
  prettyAnn MkEnvironment { prdEnv, cnsEnv, cmdEnv, declEnv } =
    vsep [ppPrds,ppCns,ppCmds, ppDecls ]
    where
      ppPrds = case M.toList prdEnv of
        [] -> mempty
        env -> vsep $ intersperse "" $ ("Producers:" : ( (\(v,(_,_,ty)) -> pretty v <+> ":" <+> prettyAnn ty) <$> env)) ++ [""]
      ppCns  = case M.toList cnsEnv of
        [] -> mempty
        env -> vsep $ intersperse "" $ ("Consumers:" : ( (\(v,(_,_,ty)) -> pretty v <+> ":" <+> prettyAnn ty) <$> env)) ++ [""]
      ppCmds = case M.toList cmdEnv of
        [] -> mempty
        env -> vsep $ intersperse "" $ ("Commands" : ( (\(v,_) -> pretty v) <$> env)) ++ [""]
      ppDecls = case declEnv of
        [] -> mempty
        env -> vsep $ intersperse "" $ ("Type declarations:" : (prettyAnn . snd <$> env)) ++ [""]

