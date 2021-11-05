module Utils where

import Data.Char (isSpace)
import Data.Foldable (foldl')
import Data.List.NonEmpty (NonEmpty(..))
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
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
  deriving (Show, Eq)

data Located a = Located Loc a

defaultLoc :: Loc
defaultLoc = Loc (SourcePos "" (mkPos 0) (mkPos 0)) (SourcePos "" (mkPos 0) (mkPos 0))

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

trimStr :: String -> String
trimStr = f . f
  where f = reverse . dropWhile isSpace

trim :: Text -> Text
trim = f . f
  where f = T.reverse . T.dropWhile isSpace


indexMaybe :: [a] -> Int -> Maybe a
indexMaybe xs i | 0 <= i && i <= (length xs) -1 = Just (xs !! i)
                | otherwise = Nothing

data Verbosity = Verbose | Silent
  deriving (Eq)
