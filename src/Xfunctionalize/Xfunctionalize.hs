module Xfunctionalize.Xfunctionalize where

-- import Data.Text qualified as T -- implementation of unicode text, qualified as T to avoid name clashes with prelude
-- import Data.Text (Text)
-- import Data.Bifunctor ( Bifunctor(bimap) )
-- import Data.Functor ( (<&>) )

-- import the needed parts of the syntax trees
import Syntax.CST.Kinds
import Syntax.CST.Names
-- import Syntax.CST.Types qualified as CST
-- import Syntax.CST.Types (PrdCnsRep(..), PrdCns(..))
-- import Syntax.RST.Terms (PrimitiveOp)
-- import Syntax.RST.Types (FlipPol, FlipPrdCns, PolarityRep(..), flipPolarityRep, flipPrdCns)
-- import Syntax.RST.Program (PrdCnsToPol)
-- import Syntax.Core.Terms (Pattern(..))
-- import Syntax.TST.Types qualified as TST
import Syntax.TST.Program qualified as TST
-- import Syntax.TST.Terms
-- import Syntax.Core.Annot
import Data.Set qualified as Set
-- import Loc -- source code locations, see src/Loc.hs


hasNestedPatternMatches :: Bool
hasNestedPatternMatches = False

dataDeclHasArguments :: TST.DataDecl -> Bool
dataDeclHasArguments decl = Set.size (allTypeVars (TST.data_kind decl)) == 0

transformable :: TST.DataDecl -> Bool
transformable = dataDeclHasArguments

