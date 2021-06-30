module Pretty.Program where

import qualified Data.Map as M
import Prettyprinter

import Pretty.Pretty
import Pretty.ATerms ()
import Pretty.STerms ()
import Pretty.Types ()
import Syntax.Program
import Syntax.Types
import Syntax.CommonTerm
import Syntax.STerms
import Syntax.ATerms
import Utils (Loc)

---------------------------------------------------------------------------------
-- Prettyprinting of Declarations
---------------------------------------------------------------------------------

instance PrettyAnn DataCodata where
  prettyAnn Data = annKeyword "data"
  prettyAnn Codata = annKeyword "codata"

instance PrettyAnn DataDecl where
  prettyAnn (NominalDecl tn dc xtors) =
    prettyAnn dc <+>
    prettyAnn tn <+>
    braces (mempty <+> cat (punctuate " , " (prettyAnn <$> xtors PosRep)) <+> mempty) <>
    semi

prettyAnnot :: Maybe (TypeScheme pol) -> Doc Annotation
prettyAnnot Nothing    = mempty
prettyAnnot (Just tys) = annSymbol ":" <+> prettyAnn tys

instance PrettyAnn a => PrettyAnn (Declaration a b) where
  prettyAnn (PrdDecl Recursive _ fv annot tm) =
    annKeyword "prd" <+> "rec" <+> pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> prettyAnn tm <> semi
  prettyAnn (PrdDecl NonRecursive _ fv annot tm) =
    annKeyword "prd" <+>           pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> prettyAnn tm <> semi
  prettyAnn (CnsDecl Recursive _ fv annot tm) =
    annKeyword "cns" <+> "rec" <+> pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> prettyAnn tm <> semi
  prettyAnn (CnsDecl NonRecursive _ fv annot tm) =
    annKeyword "cns" <+>           pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> prettyAnn tm <> semi
  prettyAnn (CmdDecl _ fv cm) =
    annKeyword "cmd" <+> pretty fv <+> annSymbol ":=" <+> prettyAnn cm <> semi
  prettyAnn (DefDecl Recursive _ fv annot tm) =
    annKeyword "def" <+> "rec" <+> pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> prettyAnn tm <> semi
  prettyAnn (DefDecl NonRecursive _ fv annot tm) =
    annKeyword "def" <+>           pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> prettyAnn tm <> semi
  prettyAnn (DataDecl _ decl) = prettyAnn decl


instance PrettyAnn (NamedRep (Declaration FreeVarName Loc)) where
  prettyAnn (NamedRep (PrdDecl Recursive _ fv annot tm)) =
    annKeyword "prd" <+> "rec" <+> pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> prettyAnn (openSTermComplete tm) <> semi
  prettyAnn (NamedRep (PrdDecl NonRecursive _ fv annot tm)) =
    annKeyword "prd" <+>           pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> prettyAnn (openSTermComplete tm) <> semi
  prettyAnn (NamedRep (CnsDecl Recursive _ fv annot tm)) =
    annKeyword "cns" <+> "rec" <+> pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> prettyAnn (openSTermComplete tm) <> semi
  prettyAnn (NamedRep (CnsDecl NonRecursive _ fv annot tm)) =
    annKeyword "cns" <+>           pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> prettyAnn (openSTermComplete tm) <> semi
  prettyAnn (NamedRep (CmdDecl _ fv cm)) =
    annKeyword "cmd" <+> pretty fv <+> annSymbol ":=" <+> prettyAnn (openCommandComplete cm) <> semi
  prettyAnn (NamedRep (DefDecl Recursive _ fv annot tm)) =
    annKeyword "def" <+> "rec" <+> pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> prettyAnn (openATermComplete tm) <> semi
  prettyAnn (NamedRep (DefDecl NonRecursive _ fv annot tm)) =
    annKeyword "def" <+>           pretty fv <+> prettyAnnot annot <+> annSymbol ":=" <+> prettyAnn (openATermComplete tm) <> semi
  prettyAnn (NamedRep (DataDecl _ decl)) = prettyAnn decl


instance {-# OVERLAPPING #-} PrettyAnn [Declaration FreeVarName] where
  prettyAnn decls = vsep (prettyAnn . NamedRep <$> decls)

---------------------------------------------------------------------------------
-- Prettyprinting of Environments
---------------------------------------------------------------------------------

instance PrettyAnn (Environment bs) where
  prettyAnn Environment { prdEnv, cnsEnv, cmdEnv, defEnv, declEnv } =
    vsep [ppPrds, "", ppCns, "", ppCmds, "",  ppDefs, "", ppDecls, ""]
    where
      ppPrds = vsep $ "Producers:" : ( (\(v,(_,ty)) -> pretty v <+> ":" <+> prettyAnn ty) <$> (M.toList prdEnv))
      ppCns  = vsep $ "Consumers:" : ( (\(v,(_,ty)) -> pretty v <+> ":" <+> prettyAnn ty) <$> (M.toList cnsEnv))
      ppCmds = vsep $ "Commands" : ( (\(v,_) -> pretty v) <$> (M.toList cmdEnv))
      ppDefs = vsep $ "Definitions:" : ( (\(v,(_,ty)) -> pretty v <+> ":" <+> prettyAnn ty) <$> (M.toList defEnv))
      ppDecls = vsep $ "Type declarations:" : (prettyAnn <$> declEnv)

