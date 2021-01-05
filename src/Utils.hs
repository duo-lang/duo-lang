module Utils where

import Data.Set (Set)
import Data.Foldable (foldl')
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.Set as S

----------------------------------------------------------------------------------
-- Twice functor
----------------------------------------------------------------------------------

-- oftenly used data structure, so extracting it and making it a functor is useful
data Twice a = Twice a a deriving (Eq,Show)
twiceMap :: (a -> b) -> (a -> b) -> Twice a -> Twice b
twiceMap f g (Twice x y) = Twice (f x) (g y)

mergeTwice :: (a -> a -> a) -> Twice a -> a
mergeTwice f (Twice x y) = f x y

instance Functor Twice where
  fmap f = twiceMap f f


data Error
  = ParseError String
  | GenConstraintsError String
  | EvalError String
  | SolveConstraintsError String
  deriving (Show, Eq)

allEq :: Eq a => [a] -> Bool
allEq [] = True
allEq (x:xs) = all (==x) xs

intersections :: Ord a => NonEmpty (Set a) -> Set a
intersections (s :| ss) = foldl' S.intersection s ss

enumerate :: [a] -> [(Int,a)]
enumerate xs = zip [0..] xs
