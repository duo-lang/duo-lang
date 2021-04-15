module Utils where

import Data.Char (isSpace)
import Data.Foldable (foldl')
import Data.List.NonEmpty (NonEmpty(..))
import Data.Set (Set)
import qualified Data.Set as S
import Text.Megaparsec.Pos

----------------------------------------------------------------------------------
-- Twice functor
----------------------------------------------------------------------------------

-- oftenly used data structure, so extracting it and making it a functor is useful
data Twice a = Twice a a deriving (Eq, Show, Ord)
twiceMap :: (a -> b) -> (a -> b) -> Twice a -> Twice b
twiceMap f g (Twice x y) = Twice (f x) (g y)

instance Functor Twice where
  fmap f = twiceMap f f

----------------------------------------------------------------------------------
-- Source code locations
----------------------------------------------------------------------------------

data Loc = Loc SourcePos SourcePos
  deriving (Show)

data Located a = Located Loc a

----------------------------------------------------------------------------------
-- Errors
----------------------------------------------------------------------------------

data Error
  = ParseError String
  | GenConstraintsError String
  | EvalError String
  | SolveConstraintsError String
  | TypeAutomatonError String
  | OtherError String
  deriving (Show, Eq)

type LocatedError = Located Error

----------------------------------------------------------------------------------
-- Helper Functions
----------------------------------------------------------------------------------

allEq :: Eq a => [a] -> Bool
allEq [] = True
allEq (x:xs) = all (==x) xs

intersections :: Ord a => NonEmpty (Set a) -> Set a
intersections (s :| ss) = foldl' S.intersection s ss

enumerate :: [a] -> [(Int,a)]
enumerate xs = zip [0..] xs

trim :: String -> String
trim = f . f
  where f = reverse . dropWhile isSpace


indexMaybe :: [a] -> Int -> Maybe a
indexMaybe xs i | 0 <= i && i <= (length xs) -1 = Just (xs !! i)
                | otherwise = Nothing

data Verbosity = Verbose | Silent
  deriving (Eq)
