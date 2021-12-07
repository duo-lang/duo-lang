module TypeAutomata.Simplify where

import Control.Monad.Except
import Control.Monad.IO.Class

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


mapError :: (MonadError e1 m1, MonadError e2 m2)
         => (e1 -> e2)
         -> m1 a -> m2 a
mapError = undefined

simplify :: (MonadIO m, MonadError Error m)
         => TypeScheme pol
         -> Bool
         -> m (SimplifyTrace pol, TypeScheme pol)
simplify tys b = do
    -- Read typescheme into automaton
    typeAut <- liftEither $ typeToAut tys
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
    tysSimplified <- liftEither $ autToType typeAutMin
    return (MkSimplifyTrace typeAutDet typeAutDet' typeAutDetAdms typeAutMin , tysSimplified)
