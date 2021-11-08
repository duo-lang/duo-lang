module TypeAutomata.Simplify where

import Errors ( Error )    
import Syntax.Types ( TypeScheme )
import TypeAutomata.Definition ( TypeAutDet, TypeAut )
import TypeAutomata.ToAutomaton ( typeToAut )
import TypeAutomata.FromAutomaton ( autToType )
import TypeAutomata.RemoveEpsilon ( removeEpsilonEdges )
import TypeAutomata.Determinize (determinize)
import TypeAutomata.RemoveAdmissible ( removeAdmissableFlowEdges )
import TypeAutomata.Minimize ( minimize )
import TypeAutomata.Lint ( lint )


data SimplifyTrace pol = MkSimplifyTrace
 { trace_typeAut        :: TypeAut pol
 , trace_typeAutDet     :: TypeAutDet pol
 , trace_typeAutDetAdms :: TypeAutDet pol
 , trace_minTypeAut     :: TypeAutDet pol
 }



simplify :: TypeScheme pol
         -> Either Error (SimplifyTrace pol, TypeScheme pol)
simplify tys = do
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
