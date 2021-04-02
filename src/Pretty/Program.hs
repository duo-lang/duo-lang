{-# LANGUAGE OverloadedStrings #-}
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
    braces (mempty <+> cat (punctuate " , " (prettyAnn <$> xtors)) <+> mempty) <>
    semi

instance PrettyAnn a => PrettyAnn (Declaration a) where
  prettyAnn (PrdDecl _ fv tm) =
    annKeyword "prd" <+> pretty fv <+> annSymbol ":=" <+> prettyAnn tm <> semi
  prettyAnn (CnsDecl _ fv tm) =
    annKeyword "cns" <+> pretty fv <+> annSymbol ":=" <+> prettyAnn tm <> semi
  prettyAnn (CmdDecl _ fv cm) =
    annKeyword "cmd" <+> pretty fv <+> annSymbol ":=" <+> prettyAnn cm <> semi
  prettyAnn (DefDecl _ fv tm) =
    annKeyword "def" <+> pretty fv <+> annSymbol ":=" <+> prettyAnn tm <> semi
  prettyAnn (DataDecl _ decl) = prettyAnn decl

instance PrettyAnn (NamedRep (Declaration FreeVarName)) where
  prettyAnn (NamedRep (PrdDecl _ fv tm)) =
    annKeyword "prd" <+> pretty fv <+> annSymbol ":=" <+> prettyAnn (openSTermComplete tm) <> semi
  prettyAnn (NamedRep (CnsDecl _ fv tm)) =
    annKeyword "cns" <+> pretty fv <+> annSymbol ":=" <+> prettyAnn (openSTermComplete tm) <> semi
  prettyAnn (NamedRep (CmdDecl _ fv cm)) =
    annKeyword "cmd" <+> pretty fv <+> annSymbol ":=" <+> prettyAnn (openCommandComplete cm) <> semi
  prettyAnn (NamedRep (DefDecl _ fv tm)) =
    annKeyword "def" <+> pretty fv <+> annSymbol ":=" <+> prettyAnn (openATermComplete tm) <> semi
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

