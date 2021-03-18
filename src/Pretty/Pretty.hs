{-# LANGUAGE OverloadedStrings #-}
module Pretty.Pretty where

import Prettyprinter
import Prettyprinter.Render.String (renderString)
import Text.Megaparsec.Pos

import Syntax.STerms
import Syntax.ATerms
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

instance Pretty a => Pretty (SCase a) where
  pretty MkSCase{..} = pretty scase_name <> prettyTwice (constString scase_args) <+> "=>" <+> pretty scase_cmd
    where
      constString :: Twice [a] -> Twice [String]
      constString (Twice a b) = Twice (const "-" <$> a) (const "-" <$> b)

instance Pretty a => Pretty (XtorArgs a) where
  pretty (MkXtorArgs prds cns) = prettyTwice' prds cns

isNumSTerm :: STerm pc a -> Maybe Int
isNumSTerm (XtorCall PrdRep (MkXtorName Nominal "Zero") (MkXtorArgs [] [])) = Just 0
isNumSTerm (XtorCall PrdRep (MkXtorName Nominal "Succ") (MkXtorArgs [n] [])) = case isNumSTerm n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumSTerm _ = Nothing

instance Pretty a => Pretty (STerm pc a) where
  pretty (isNumSTerm -> Just n) = pretty n -- View Pattern !
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

isNumATerm :: ATerm a -> Maybe Int
isNumATerm (Ctor (MkXtorName Nominal "Zero") []) = Just 0
isNumATerm (Ctor (MkXtorName Nominal "Succ") [n]) = case isNumATerm n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumATerm _ = Nothing

instance Pretty a => Pretty (ACase a) where
  pretty MkACase{ acase_name, acase_args, acase_term } =
    pretty acase_name <> parens (intercalateComma (map (const "-") acase_args)) <+> "=>" <+> pretty acase_term

instance Pretty a => Pretty (ATerm a) where
  pretty (isNumATerm -> Just n) = pretty n -- View Pattern !
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

instance Pretty (Typ pol) where
  pretty (TySet PosRep []) = "Bot"
  pretty (TySet PosRep [t]) = pretty t
  pretty (TySet PosRep tts) = parens (intercalateX " \\/ " (map pretty tts))
  pretty (TySet NegRep []) = "Top"
  pretty (TySet NegRep [t]) = pretty t
  pretty (TySet NegRep tts) = parens (intercalateX " /\\ " (map pretty tts))
  pretty (TyVar _ _ tv) = pretty tv -- Normal + Recursive
  pretty (TyRec _ rv t) = "rec " <> pretty rv <> "." <> pretty t
  pretty (TyNominal _ tn) = pretty (unTypeName tn)
  pretty (TyStructural _ DataRep   xtors) = angles (mempty <+> cat (punctuate " | " (pretty <$> xtors)) <+> mempty)
  pretty (TyStructural _ CodataRep xtors) = braces (mempty <+> cat (punctuate " , " (pretty <$> xtors)) <+> mempty)

instance Pretty (TypArgs a) where
  pretty (MkTypArgs prdArgs cnsArgs) = prettyTwice' prdArgs cnsArgs

instance Pretty (XtorSig a) where
  pretty (MkXtorSig xt args) = pretty xt <> pretty args

instance Pretty (TypeScheme pol) where
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

instance Pretty Pos where
  pretty p = pretty (unPos p)

instance Pretty Loc where
  pretty (Loc (SourcePos fp line1 column1) (SourcePos _ line2 column2)) =
    pretty fp <> ":" <> pretty line1 <> ":" <> pretty column1 <> "-" <> pretty line2 <> ":" <> pretty column2

instance Pretty LocatedError where
  pretty (Located loc err) = vsep ["Error at:" <+> pretty loc, pretty err]

