module TypeAutomata.Subsume ( subsume ) where

import Data.Graph.Inductive.Graph

import Data.List.NonEmpty (NonEmpty)

import Data.Maybe (fromJust)
import Data.Functor.Identity

import Errors
import Syntax.TST.Types
import Syntax.RST.Types (PolarityRep(..), Polarity(..))
import TypeAutomata.Definition
import TypeAutomata.ToAutomaton (typeToAut)
import TypeAutomata.Determinize (determinize)
import TypeAutomata.RemoveEpsilon ( removeEpsilonEdges )
import TypeAutomata.RemoveAdmissible ( removeAdmissableFlowEdges )
import TypeAutomata.Minimize (minimize)
import TypeAutomata.Utils (typeAutEqual)



-- Shift up all the nodes of the graph by the given number. Generates an isomorphic graph.
shiftGraph :: Int -> TypeAutDet pol -> TypeAutDet pol
shiftGraph shift = mapTypeAut (+shift)

-- Constructs the union of two TypeAuts, assumes that the node ranges don't overlap.
unsafeUnion :: TypeAutDet pol -> TypeAutDet pol -> TypeAut pol
unsafeUnion (TypeAut polrep (Identity starts1) (TypeAutCore gr1 flowEdges1))
            (TypeAut _      (Identity starts2) (TypeAutCore gr2 flowEdges2)) =
  TypeAut { ta_pol = polrep
          , ta_starts = [starts1, starts2]
          , ta_core = TypeAutCore
            { ta_gr = mkGraph (labNodes gr1 ++ labNodes gr2) (labEdges gr1 ++ labEdges gr2)
            , ta_flowEdges = flowEdges1 ++ flowEdges2
            }
          }

-- Constructs the union of two TypeAuts
typeAutUnion :: TypeAutDet pol -> TypeAutDet pol -> TypeAut pol
typeAutUnion aut1@TypeAut{..} aut2 = unsafeUnion aut1 (shiftGraph shift aut2)
  where
    shift = 1 + snd (nodeRange (ta_gr ta_core))

isSubtype :: TypeAutDet pol -> TypeAutDet pol -> Bool
isSubtype aut1 aut2 = case (startPolarity aut1, startPolarity aut2) of
  (Pos,Pos) -> fun (typeAutUnion aut1 aut2) `typeAutEqual` aut2
  (Neg,Neg) -> fun (typeAutUnion aut1 aut2) `typeAutEqual` aut1
  _         -> error "isSubtype: only defined for types of equal polarity."
  where
    startPolarity TypeAut{..} = getPolarityNL (fromJust (lab (ta_gr ta_core) (runIdentity ta_starts)))
    fun = minimize . removeAdmissableFlowEdges . determinize

subsume :: PolarityRep pol -> TypeScheme pol -> TypeScheme pol -> Either (NonEmpty Error) Bool
subsume polrep ty1 ty2 = do
  aut1 <- minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges <$> typeToAut ty1
  aut2 <- minimize . removeAdmissableFlowEdges . determinize . removeEpsilonEdges <$> typeToAut ty2
  case polrep of
    PosRep -> pure (isSubtype aut1 aut2)
    NegRep -> pure (isSubtype aut2 aut1)
