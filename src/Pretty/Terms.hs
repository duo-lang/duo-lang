module Pretty.Terms where

import Data.List.NonEmpty (NonEmpty(..))
import Data.List.NonEmpty qualified as NE
import Prettyprinter

import Pretty.Pretty
import Syntax.Terms
import Syntax.CommonTerm



---------------------------------------------------------------------------------
-- Terms
---------------------------------------------------------------------------------

instance PrettyAnn (SCase ext) where
  prettyAnn MkSCase{..} =
    let
      prds = [x | (Prd,x) <- scase_args]
      cnss = [x | (Cns,x) <- scase_args]
    in
      prettyAnn scase_name <>
      prettyTwice prds cnss <+>
      annSymbol "=>" <+>
      prettyAnn scase_cmd

instance PrettyAnn (ACase ext) where
  prettyAnn MkACase{ acase_name, acase_args, acase_term } =
    let
      prds = [x | (Prd,x) <- acase_args]
      cnss = [x | (Cns,x) <- acase_args]
    in
      prettyAnn acase_name <>
      prettyTwice prds cnss <+>
      annSymbol "=>" <+>
      prettyAnn acase_term

instance PrettyAnn (PrdCnsTerm ext) where
  prettyAnn (PrdTerm tm) = prettyAnn tm
  prettyAnn (CnsTerm tm) = prettyAnn tm

splitSubst :: Substitution ext -> [NonEmpty (PrdCnsTerm ext)]
splitSubst = NE.groupBy f
  where
    f :: PrdCnsTerm ext -> PrdCnsTerm ext -> Bool
    f (PrdTerm _) (PrdTerm _) = True
    f (CnsTerm _) (CnsTerm _) = True
    f _ _ = False

printSegment :: NonEmpty (PrdCnsTerm ext) -> Doc Annotation
printSegment (PrdTerm e :| rest) = parens'   comma (prettyAnn <$> PrdTerm e : rest)
printSegment (CnsTerm e :| rest) = brackets' comma (prettyAnn <$> CnsTerm e : rest)


instance {-# OVERLAPPING #-} PrettyAnn (Substitution ext) where
  prettyAnn subst = mconcat (printSegment <$> splitSubst subst)

isNumSTerm :: Term pc ext -> Maybe Int
isNumSTerm (XtorCall _ PrdRep (MkXtorName Nominal "Z") []) = Just 0
isNumSTerm (XtorCall _ PrdRep (MkXtorName Nominal "S") [PrdTerm n]) = case isNumSTerm n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumSTerm _ = Nothing

instance PrettyAnn (Term pc ext) where
  prettyAnn (isNumSTerm -> Just n) = pretty n
  prettyAnn (BoundVar _ _ (i,j)) = parens (pretty i <> "," <> pretty j)
  prettyAnn (FreeVar _ _ v) = pretty v
  prettyAnn (XtorCall _ _ xt args) = prettyAnn xt <> prettyAnn args
  prettyAnn (XMatch _ PrdRep _ cases) =
    annKeyword "comatch" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (XMatch _ CnsRep _ cases) =
    annKeyword "match"   <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (MuAbs _ pc a cmd) =
    annKeyword (case pc of {PrdRep -> "mu"; CnsRep -> "mu"}) <+>
    prettyAnn a <> "." <> parens (prettyAnn cmd)
  prettyAnn (Dtor _ xt t args) =
    parens ( prettyAnn t <> "." <> prettyAnn xt <> parens (intercalateComma (map prettyAnn args)))
  prettyAnn (Match _ _ t cases) =
    annKeyword "case" <+>
    prettyAnn t <+>
    annKeyword "of" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cases)))))
  prettyAnn (Comatch _ _ cocases) =
    annKeyword "cocase" <+>
    braces (group (nest 3 (line' <> vsep (punctuate comma (prettyAnn <$> cocases)))))

instance PrettyAnn (Command ext) where
  prettyAnn (Done _)= annKeyword "Done"
  prettyAnn (Print _ t) = annKeyword "Print" <> parens (prettyAnn t)
  prettyAnn (Apply _ t1 t2) = group (nest 3 (line' <> vsep [prettyAnn t1, annSymbol ">>", prettyAnn t2]))

instance PrettyAnn (NamedRep (Term pc ext)) where
  prettyAnn (NamedRep tm) = prettyAnn (openTermComplete tm)

instance PrettyAnn (NamedRep (Command ext)) where
  prettyAnn (NamedRep cmd) = prettyAnn (openCommandComplete cmd)

