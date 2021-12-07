module TypeAutomata.Simplify where

import Errors ( Error(..) )    
import Syntax.Types
import Syntax.Kinds
import TypeAutomata.Definition ( TypeAutDet, TypeAut )
import TypeAutomata.ToAutomaton ( typeToAut )
import TypeAutomata.FromAutomaton ( autToType )
import TypeAutomata.RemoveEpsilon ( removeEpsilonEdges )
import TypeAutomata.Determinize (determinize)
import TypeAutomata.RemoveAdmissible ( removeAdmissableFlowEdges )
import TypeAutomata.Minimize ( minimize )
import TypeAutomata.Lint ( lint )
import Utils (allEq)


data SimplifyTrace pol = MkSimplifyTrace
 { trace_typeAut        :: TypeAut pol
 , trace_typeAutDet     :: TypeAutDet pol
 , trace_typeAutDetAdms :: TypeAutDet pol
 , trace_minTypeAut     :: TypeAutDet pol
 }



simplify :: TypeScheme pol
         -> Either Error (SimplifyTrace pol, TypeScheme pol)
simplify tys = do
    -- Check that input type is kind correct
    kindCheckTypeScheme tys
    -- Read typescheme into automaton
    typeAut <- typeToAut tys
    lint typeAut
    -- Remove epsilon edges
    let typeAutDet = removeEpsilonEdges typeAut
    lint typeAutDet
    -- Determinize the automaton
    let typeAutDet' = determinize typeAutDet
    lint typeAutDet'
    -- Remove admissable flow edges
    let typeAutDetAdms = removeAdmissableFlowEdges typeAutDet'
    lint typeAutDetAdms
    -- Minimize automaton
    let typeAutMin = minimize typeAutDetAdms
    lint typeAutMin
    -- Read back to type
    tysSimplified <- autToType typeAutMin
    return (MkSimplifyTrace typeAutDet typeAutDet' typeAutDetAdms typeAutMin , tysSimplified)


kindCheckTypeScheme :: TypeScheme pol -> Either Error ()
kindCheckTypeScheme (TypeScheme tvars monotype) = kindCheckType tvars monotype

kindCheckType :: [(TVar, Kind)] -> Typ pol -> Either Error ()
kindCheckType _ (TyVar _ Nothing _) = Left (OtherError "KindCheck: Type variable not annotated.")
kindCheckType env (TyVar _ (Just kind) tv) = case lookup tv env of
    Nothing -> Left (OtherError "Foo")
    Just kind' -> if kind == kind' then return () else Left (OtherError "KindCheck: Type variable is annotated with different kind from context.")
kindCheckType env (TyData _ _ xtors)   = sequence_ $ kindCheckXtors env <$> xtors
kindCheckType env (TyCodata _ _ xtors) = sequence_ $ kindCheckXtors env <$> xtors
kindCheckType _ (TyNominal _ Nothing _) = Left (OtherError "KindCheck: TyNominal not annotated.")
kindCheckType _ (TyNominal _ (Just _) _) = return ()
kindCheckType _ (TySet _ Nothing _) = Left (OtherError "KindCheck: TySet not annotated.")
kindCheckType _ (TySet _ (Just kind) typs) = do
    let kinds = getKind <$> typs
    if allEq (kind:kinds)
        then return ()
        else Left (OtherError "KindCheck: TySet contains different kinds.")
kindCheckType env (TyRec _ tv ty) = kindCheckType ((tv, getKind ty) : env) ty
    
kindCheckPrdCnsType :: [(TVar, Kind)] -> PrdCnsType pol -> Either Error ()
kindCheckPrdCnsType env (PrdType ty) = kindCheckType env ty
kindCheckPrdCnsType env (CnsType ty) = kindCheckType env ty

kindCheckXtors :: [(TVar, Kind)] -> XtorSig pol -> Either Error ()
kindCheckXtors env (MkXtorSig _ args) = sequence_ $ kindCheckPrdCnsType env <$> args