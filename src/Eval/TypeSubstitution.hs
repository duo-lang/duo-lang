module Eval.TypeSubstitution where

import Syntax.Types
import Utils

---------------------------------------------------------------------------------
-- Variable Opening
---------------------------------------------------------------------------------

typeOpeningRec :: Int -> Typ a -> Typ a -> Typ a
typeOpeningRec k ty bv@(TyBoundVar (MkUVar i)) | i == k = ty
                                               | otherwise = bv
typeOpeningRec _ _ fv@(TyFreeVar _) = fv
typeOpeningRec _ _ ty@(TyNominal _) = ty
typeOpeningRec k ty (TySet v ui tys) = TySet v ui (typeOpeningRec k ty <$> tys)
typeOpeningRec k ty (TySimple dc xtors) = TySimple dc (xtorOpeningRec k ty <$> xtors)
typeOpeningRec k ty (TyRec v ty') = TyRec v (typeOpeningRec (k + 1) ty ty')

xtorOpeningRec :: Int -> Typ a -> XtorSig (Typ a) -> XtorSig (Typ a)
xtorOpeningRec k ty MkXtorSig { sig_name, sig_args = Twice prdArgs cnsArgs } =
  MkXtorSig sig_name (Twice (typeOpeningRec k ty <$> prdArgs) (typeOpeningRec k ty <$> cnsArgs))

typeOpening :: Typ a -> Typ a -> Typ a
typeOpening = typeOpeningRec 0

---------------------------------------------------------------------------------
-- Variable Closing
---------------------------------------------------------------------------------

typeClosingRec :: Int -> TVar -> Typ a -> Typ a
typeClosingRec _ _ ty@(TyBoundVar _) = ty
typeClosingRec k fv ty@(TyFreeVar fv') | fv == fv' = TyBoundVar (MkUVar k)
                                       | otherwise = ty
typeClosingRec _ _ ty@(TyNominal _) = ty
typeClosingRec k fv (TySet v ui tys) = TySet v ui (typeClosingRec k fv <$> tys)
typeClosingRec k fv (TySimple dc xtors) = TySimple dc (xtorClosingRec k fv <$> xtors)
typeClosingRec k fv (TyRec v ty) = TyRec v (typeClosingRec (k + 1) fv ty)

xtorClosingRec :: Int -> TVar -> XtorSig (Typ a) -> XtorSig (Typ a)
xtorClosingRec k ty MkXtorSig { sig_name, sig_args = Twice prdArgs cnsArgs } =
  MkXtorSig sig_name (Twice (typeClosingRec k ty <$> prdArgs) (typeClosingRec k ty <$> cnsArgs))

typeClosing :: TVar -> Typ a -> Typ a
typeClosing = typeClosingRec 0

---------------------------------------------------------------------------------
-- Free variables
---------------------------------------------------------------------------------

typeFreeVars :: Typ a -> [TVar]
typeFreeVars (TyFreeVar fv) = [fv]
typeFreeVars (TyBoundVar _) = []
typeFreeVars (TyNominal _) = []
typeFreeVars (TySimple _ xtors) = concat (xtorFreeVars <$> xtors)
typeFreeVars (TySet _ _ tys) = concat (typeFreeVars <$> tys)
typeFreeVars (TyRec _ ty) = typeFreeVars ty

xtorFreeVars :: XtorSig (Typ a) -> [TVar]
xtorFreeVars MkXtorSig { sig_args = Twice prdArgs cnsArgs } =
  concat ((typeFreeVars <$> prdArgs) ++ (typeFreeVars <$> cnsArgs))
