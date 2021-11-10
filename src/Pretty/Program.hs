module Pretty.Program where

import Data.Map qualified as M
import Prettyprinter

import Data.List (intersperse)

import Pretty.Pretty
import Pretty.ATerms ()
import Pretty.STerms ()
import Pretty.Types ()
import Syntax.Program
import Syntax.Types
import Syntax.STerms
import Syntax.ATerms

---------------------------------------------------------------------------------
-- Prettyprinting of Declarations
---------------------------------------------------------------------------------

instance PrettyAnn DataCodata where
  prettyAnn Data = annKeyword "data"
  prettyAnn Codata = annKeyword "codata"

instance PrettyAnn DataDecl where
  prettyAnn (NominalDecl tn dc knd xtors) =
    prettyAnn dc <+>
    prettyAnn tn <+>
    colon <+>
    prettyAnn knd <+>
    braces (mempty <+> cat (punctuate " , " (prettyAnn <$> xtors PosRep)) <+> mempty) <>
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

prettyDefDecl :: Pretty a => IsRec -> a -> Maybe (TypeScheme pol) -> Doc Annotation -> Doc Annotation
prettyDefDecl Recursive    fv annot ptm =
  annKeyword "def" <+> "rec" <+> pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> ptm <> semi
prettyDefDecl NonRecursive fv annot ptm =
  annKeyword "def" <+>           pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> ptm <> semi

instance PrettyAnn (Declaration ext) where
  prettyAnn (PrdCnsDecl _ pc isRec fv annot tm) =
    prettyPrdCnsDecl pc isRec fv annot (prettyAnn tm)
  prettyAnn (CmdDecl _ fv cm) =
    prettyCmdDecl fv (prettyAnn cm)
  prettyAnn (DefDecl _ isRec fv annot tm) =
    prettyDefDecl isRec fv annot (prettyAnn tm)
  prettyAnn (DataDecl _ decl) =
    prettyAnn decl
  prettyAnn (ImportDecl _ mod) =
    annKeyword "import" <+> prettyAnn mod <> semi
  prettyAnn (SetDecl _ txt) =
    annKeyword "set" <+> prettyAnn txt <> semi
  prettyAnn ParseErrorDecl =
    "<ParseError>"


instance PrettyAnn (NamedRep (Declaration ext)) where
  prettyAnn (NamedRep (PrdCnsDecl _ pc isRec fv annot tm)) =
    prettyPrdCnsDecl pc isRec fv annot (prettyAnn (openSTermComplete tm))
  prettyAnn (NamedRep (CmdDecl _ fv cm)) =
    prettyCmdDecl fv (prettyAnn (openCommandComplete cm))
  prettyAnn (NamedRep (DefDecl _ isRec fv annot tm)) =
    prettyDefDecl isRec fv annot (prettyAnn (openATermComplete tm))
  prettyAnn (NamedRep (DataDecl _ decl)) =
    prettyAnn decl
  prettyAnn (NamedRep (ImportDecl _ mod)) =
    annKeyword "import" <+> prettyAnn mod <> semi
  prettyAnn (NamedRep (SetDecl _ txt)) =
    annKeyword "set" <+> prettyAnn txt <> semi
  prettyAnn (NamedRep ParseErrorDecl) =
    "<ParseError>"


instance {-# OVERLAPPING #-} PrettyAnn [Declaration Parsed] where
  prettyAnn decls = vsep (prettyAnn . NamedRep <$> decls)

instance {-# OVERLAPPING #-} PrettyAnn [Declaration Inferred] where
  prettyAnn decls = vsep (prettyAnn . NamedRep <$> decls)

---------------------------------------------------------------------------------
-- Prettyprinting of Environments
---------------------------------------------------------------------------------

instance PrettyAnn Environment where
  prettyAnn Environment { prdEnv, cnsEnv, cmdEnv, defEnv, declEnv } =
    vsep [ppPrds, "", ppCns, "", ppCmds, "",  ppDefs, "", ppDecls, ""]
    where
      ppPrds = vsep $ intersperse "" $ "Producers:" : ( (\(v,(_,_,ty)) -> pretty v <+> ":" <+> prettyAnn ty) <$> (M.toList prdEnv))
      ppCns  = vsep $ intersperse "" $ "Consumers:" : ( (\(v,(_,_,ty)) -> pretty v <+> ":" <+> prettyAnn ty) <$> (M.toList cnsEnv))
      ppCmds = vsep $ intersperse "" $ "Commands" : ( (\(v,_) -> pretty v) <$> (M.toList cmdEnv))
      ppDefs = vsep $ intersperse "" $ "Definitions:" : ( (\(v,(_,_,ty)) -> pretty v <+> ":" <+> prettyAnn ty) <$> (M.toList defEnv))
      ppDecls = vsep $ intersperse "" $ "Type declarations:" : (prettyAnn . snd <$> declEnv)

