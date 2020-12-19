module Syntax.Utils where

import Utils
import Syntax.Types
import Eval.TypeSubstitution

-- Helpers for deprecating old target types.

oldToNew :: TargetType -> TargetType'
oldToNew (TTyVar _ tv) = TyFreeVar tv
oldToNew (TTySet ui ts) = TySet () ui (oldToNew <$> ts)
oldToNew (TTyRec tv ts) = TyRec () (typeClosing tv (oldToNew ts))
oldToNew (TTySimple dc xtors) = TySimple dc (oldToNewXtor <$> xtors)
  where
    oldToNewXtor (MkXtorSig xt (Twice prdTypes cnsTypes)) = MkXtorSig xt (Twice (oldToNew <$> prdTypes) (oldToNew <$> cnsTypes))
oldToNew (TTyNominal tn) = TyNominal tn


closeAll :: [TVar] -> Typ a -> Typ a
closeAll [] typ = typ
closeAll (tv:tvs) typ = typeClosing tv (closeAll tvs typ)

oldToNew' :: TypeScheme -> TypeScheme'
oldToNew' TypeScheme { ts_vars, ts_monotype } =
  let
    ts_monotype' = oldToNew ts_monotype
  in
    TypeScheme' { ts_vars' = (const ()) <$> ts_vars
                , ts_monotype' = closeAll ts_vars ts_monotype'
                }

