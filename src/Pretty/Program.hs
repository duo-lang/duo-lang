module Pretty.Program where

import Data.List (intersperse)
import Data.Map qualified as M
import Prettyprinter

import Driver.Environment
import Pretty.Common
import Pretty.Pretty
import Pretty.Terms ()
import Pretty.Types ()
import Syntax.Common
import Syntax.Common.TypesUnpol qualified as UnPol
import Syntax.Common.TypesPol qualified as Pol
import Syntax.Core.Program qualified as Core
import Syntax.CST.Program qualified as CST
import Syntax.RST.Program qualified as RST
import Syntax.TST.Program qualified as TST
import Translate.Embed
import Translate.Reparse

---------------------------------------------------------------------------------
-- Prettyprinting of Declarations
---------------------------------------------------------------------------------

instance PrettyAnn UnPol.DataDecl where
  prettyAnn (UnPol.NominalDecl ref tn dc knd xtors) =
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

prettyAnnot :: Maybe UnPol.TypeScheme -> Doc Annotation
prettyAnnot Nothing    = mempty
prettyAnnot (Just tys) = annSymbol ":" <+> prettyAnn tys

prettyPrdCnsDecl :: PrettyAnn a => PrdCns -> IsRec -> a -> Maybe UnPol.TypeScheme -> Doc Annotation -> Doc Annotation
prettyPrdCnsDecl pc Recursive fv annot ptm =
  annKeyword "def" <+> "rec" <+> prettyPrdCns pc <+> prettyAnn fv   <+> prettyAnnot annot <+> annSymbol ":=" <+> ptm <> semi
prettyPrdCnsDecl pc NonRecursive fv annot ptm =
  annKeyword "def" <+>        prettyPrdCns pc <+>   prettyAnn fv <+>  prettyAnnot annot <+> annSymbol ":=" <+> ptm <> semi

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

-- | Prettyprint list of type variables for class declaration.
prettyTVars :: [(Variance, TVar, MonoKind)] -> Doc Annotation
prettyTVars tvs =
  parens
    $   mempty
    <+> cat
          (punctuate
            comma
            (   (\(var, v, k) -> prettyAnn var <> prettyAnn v <+> annSymbol ":" <+> prettyAnn k)
            <$> tvs
            )
          )
    <+> mempty

-- | Prettyprint list of xtors for class declaration.
prettyXTors :: [(XtorName, [(PrdCns, UnPol.Typ)])] -> Doc Annotation
prettyXTors xtors = braces $ group
  (nest
    3
    (line' <> vsep
      (punctuate
        comma
        (   (\(nm, ts) ->
              prettyAnn nm <> parens
                (cat $ (\(pc, t) -> prettyAnn pc <+> prettyAnn t) <$> ts)
            )
        <$> xtors
        )
      )
    )
  )

instance PrettyAnn ClassName where
  prettyAnn nm = prettyAnn nm

instance PrettyAnn Core.Declaration where
  prettyAnn decl = prettyAnn (embedCoreDecl decl)

instance PrettyAnn TST.Declaration where
  prettyAnn decl = prettyAnn (embedASTDecl decl)

instance PrettyAnn RST.Declaration where
  prettyAnn decl = prettyAnn (reparseDecl decl)

    
instance PrettyAnn CST.Declaration where
  prettyAnn (CST.PrdCnsDecl _ _ pc isRec fv annot tm) =
    prettyPrdCnsDecl pc isRec fv annot (prettyAnn tm)
  prettyAnn (CST.CmdDecl _ _ fv cm) =
    prettyCmdDecl fv (prettyAnn cm)
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
  prettyAnn (CST.ClassDecl _ _ nm tvs xtors) =
    annKeyword "class" <+> prettyAnn nm <+>
    prettyTVars tvs <+> 
    prettyXTors xtors <>
    semi
  prettyAnn (CST.InstanceDecl _ _ nm ty cases) =
    annKeyword "instance" <+> prettyAnn nm <+> prettyAnn ty <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases))))) <>
    semi
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

