{-# LANGUAGE OverloadedStrings #-}
module Pretty.Pretty where

import Prettyprinter
import Prettyprinter.Render.String (renderString)

import Syntax.SymmetricTerm
import Syntax.AsymmetricTerm
import Syntax.Types
import Utils

---------------------------------------------------------------------------------
-- Helper functions
---------------------------------------------------------------------------------

ppPrint :: Pretty a => a -> String
ppPrint doc = renderString (layoutPretty defaultLayoutOptions { layoutPageWidth = AvailablePerLine 100 1 }(pretty doc))

intercalateX :: Doc ann -> [Doc ann] -> Doc ann
intercalateX  x xs = cat (punctuate x xs)

intercalateComma :: [Doc ann] -> Doc ann
intercalateComma xs = cat (punctuate comma xs)

prettyTwice' :: (Pretty a, Pretty b) => [a] -> [b] -> Doc ann
prettyTwice' xs ys = xs' <> ys'
  where
    xs' = if null xs then mempty else parens   (intercalateComma (map pretty xs))
    ys' = if null ys then mempty else brackets (intercalateComma (map pretty ys))

prettyTwice :: Pretty a => Twice [a] -> Doc ann
prettyTwice (Twice xs ys) = prettyTwice' xs ys

instance Pretty XtorName where
  pretty (MkXtorName Structural xt) = "'" <> pretty xt
  pretty (MkXtorName Nominal    xt) = pretty xt

---------------------------------------------------------------------------------
-- Symmetric Terms
---------------------------------------------------------------------------------

instance Pretty a => Pretty (Case a) where
  pretty MkCase{..} = pretty case_name <> prettyTwice (constString case_args) <+> "=>" <+> pretty case_cmd
    where
      constString :: Twice [a] -> Twice [String]
      constString (Twice a b) = Twice (const "-" <$> a) (const "-" <$> b)

instance Pretty a => Pretty (XtorArgs a) where
  pretty (MkXtorArgs prds cns) = prettyTwice' prds cns

isNum :: Term pc a -> Maybe Int
isNum (XtorCall PrdRep (MkXtorName Structural "Z") (MkXtorArgs [] [])) = Just 0
isNum (XtorCall PrdRep (MkXtorName Structural "S") (MkXtorArgs [n] [])) = case isNum n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNum _ = Nothing

instance Pretty a => Pretty (Term pc a) where
  pretty (isNum -> Just n) = pretty n -- View Pattern !
  pretty (BoundVar _ (i,j)) = parens (pretty i <> "," <> pretty j)
  pretty (FreeVar _ v a) = parens (pretty v <+> ":" <+> pretty a)
  pretty (XtorCall _ xt args) = pretty xt <> pretty args
  pretty (XMatch PrdRep _ cases) = "comatch" <+> braces (group (nest 3 (line' <> vsep (punctuate comma (pretty <$> cases)))))
  pretty (XMatch CnsRep _ cases) = "match"   <+> braces (group (nest 3 (line' <> vsep (punctuate comma (pretty <$> cases)))))
  pretty (MuAbs pc a cmd) =
    case pc of {PrdRep -> "mu"; CnsRep -> "mu*"} <> brackets (pretty a) <> "." <> parens (pretty cmd)

instance Pretty a => Pretty (Command a) where
  pretty Done = "Done"
  pretty (Print t) = "Print" <> parens (pretty t)
  pretty (Apply t1 t2) = group (nest 3 (line' <> vsep [pretty t1, ">>", pretty t2]))

---------------------------------------------------------------------------------
-- Asymmetric Terms
---------------------------------------------------------------------------------

instance Pretty a => Pretty (ACase a) where
  pretty MkACase{ acase_name, acase_args, acase_term } =
    pretty acase_name <> parens (intercalateComma (map (const "-") acase_args)) <+> "=>" <+> pretty acase_term

instance Pretty a => Pretty (ATerm a) where
  pretty (BVar (i,j)) = parens (pretty i <> "," <> pretty j)
  pretty (FVar v) = pretty v
  pretty (Ctor xt args) = pretty xt <> parens (intercalateComma (map pretty args))
  pretty (Dtor xt t args) = parens ( pretty t <> "." <> pretty xt <> parens (intercalateComma (map pretty args)))
  pretty (Match t cases) = "match" <+> pretty t <+> "with" <+> braces (group (nest 3 (line' <> vsep (punctuate comma (pretty <$> cases)))))
  pretty (Comatch cocases) = "comatch" <+> braces (group (nest 3 (line' <> vsep (punctuate comma (pretty <$> cocases)))))

---------------------------------------------------------------------------------
-- Prettyprinting of Types
---------------------------------------------------------------------------------

instance Pretty TVar where
  pretty (MkTVar tv) = pretty tv

instance Pretty a => Pretty (XtorSig a) where
  pretty (MkXtorSig xt args) = pretty xt <> prettyTwice args

instance Pretty (Typ a) where
  pretty (TySet _ Union []) = "Bot"
  pretty (TySet _ Union [t]) = pretty t
  pretty (TySet _ Union tts) = parens (intercalateX " \\/ " (map pretty tts))
  pretty (TySet _ Inter []) = "Top"
  pretty (TySet _ Inter [t]) = pretty t
  pretty (TySet _ Inter tts) = parens (intercalateX " /\\ " (map pretty tts))
  pretty (TyVar _ tv) = pretty tv -- Normal + Recursive
  pretty (TyRec _ rv t) = "rec " <> pretty rv <> "." <> pretty t
  pretty (TyNominal tn) = pretty (unTypeName tn)
  pretty (TySimple Data   xtors) = angles (mempty <+> cat (punctuate " | " (pretty <$> xtors)) <+> mempty)
  pretty (TySimple Codata xtors) = braces (mempty <+> cat (punctuate " , " (pretty <$> xtors)) <+> mempty)

instance Pretty TypeScheme where
  pretty (TypeScheme [] ty) = pretty ty
  pretty (TypeScheme tvs ty) = "forall " <> intercalateX "" (map pretty tvs) <> ". " <> pretty ty

instance Pretty Constraint where
  pretty (SubType t1 t2) = pretty t1 <+> "<:" <+> pretty t2

instance Pretty TypeName where
  pretty (MkTypeName tn) = pretty tn

instance Pretty DataDecl where
  pretty (NominalDecl tn Data xtors)   = "data" <+> pretty tn <+> braces (mempty <+> cat (punctuate " , " (pretty <$> xtors)) <+> mempty)
  pretty (NominalDecl tn Codata xtors) = "codata" <+> pretty tn <+> braces (mempty <+> cat (punctuate " , " (pretty <$> xtors)) <+> mempty)

---------------------------------------------------------------------------------
-- Prettyprinting of Errors
---------------------------------------------------------------------------------

instance Pretty Error where
  pretty (ParseError err) = "Parsing error:" <+> pretty err
  pretty (EvalError err) = "Evaluation error:" <+> pretty err
  pretty (GenConstraintsError err) = "Constraint generation error:" <+> pretty err
  pretty (SolveConstraintsError err) = "Constraint solving error:" <+> pretty err
  pretty (OtherError err) = "Other Error:" <+> pretty err

