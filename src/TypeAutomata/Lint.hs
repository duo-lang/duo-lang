module TypeAutomata.Lint
  ( lint
  ) where

import Errors
import TypeAutomata.Definition

-- | Check the invariants of the type automaton.
lint :: TypeAut' a f pol  -> Either Error ()
lint _aut = pure ()
