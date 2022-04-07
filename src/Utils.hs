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
-- Source code locations
----------------------------------------------------------------------------------

data Loc = Loc SourcePos SourcePos
  deriving (Show, Eq, Ord)

defaultLoc :: Loc
defaultLoc = Loc (SourcePos "" (mkPos 1) (mkPos 1)) (SourcePos "" (mkPos 1) (mkPos 1))

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
