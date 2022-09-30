module Utils
  ( -- Helper functions
    intersections
  , enumerate
  , trimStr
  , trim
  , indexMaybe
  , mapAppend
    -- Verbosity
  , Verbosity(..)
    -- Directory helper functions
  , listRecursiveFiles
  , listRecursiveDuoFiles
  , isDuoFile
  , analyzeDuoFilepath
  , filePathToModuleName
  ) where

import Control.Monad (forM)
import Data.Char (isSpace)
import Data.Foldable (foldl')
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import System.Directory ( listDirectory, doesDirectoryExist)
import System.FilePath (takeExtension, splitFileName, splitDirectories, dropExtension, takeBaseName)
import Syntax.CST.Names (ModuleName (..))
import Control.Arrow (second)

----------------------------------------------------------------------------------
-- Helper Functions
----------------------------------------------------------------------------------

intersections :: Ord a => NonEmpty (Set a) -> Set a
intersections (s :| ss) = foldl' S.intersection s ss

enumerate :: [a] -> [(Int,a)]
enumerate = zip [0..]

trimStr :: String -> String
trimStr = f . f
  where f = reverse . dropWhile isSpace

trim :: Text -> Text
trim = f . f
  where f = T.reverse . T.dropWhile isSpace


indexMaybe :: [a] -> Int -> Maybe a
indexMaybe xs i | 0 <= i && i <= length xs -1 = Just (xs !! i)
                | otherwise = Nothing

data Verbosity = Verbose | Silent
  deriving (Eq)

-- Maps
mapAppend :: (Ord k, Semigroup m) => k -> m -> Map k m -> Map k m
mapAppend k a = M.alter (\case
                              Nothing -> Just a
                              Just b  -> Just $ a <> b)
                        k
----------------------------------------------------------------------------------
-- Directory helper functions
----------------------------------------------------------------------------------

filePathToModuleName :: FilePath -> ModuleName
filePathToModuleName fp = 
    let name = T.pack (takeBaseName fp)
        path = T.pack <$> case init $ splitDirectories fp of
                            []     -> []
                            "/":xs -> xs
                            xs     -> xs
    in  MkModuleName path name


-- | Given a filepath pointing to a directory, list all files which are recursively
-- reachable from that directory.
-- The output contains a list of only files, not directories.
-- Special directories "." and ".." are not contained in the output.
listRecursiveFiles :: FilePath -> IO [(FilePath, FilePath)]
listRecursiveFiles topdir = do
  names <- listDirectory topdir
  paths <- forM names $ \name -> do
    isDirectory <- doesDirectoryExist topdir
    if isDirectory
      then listRecursiveFiles topdir
      else pure [(topdir, name)]
  pure (concat paths)


listRecursiveDuoFiles :: FilePath -> IO [(FilePath, ModuleName)]
listRecursiveDuoFiles fp = do
  exists <- doesDirectoryExist fp
  if exists
  then do
    files <- listRecursiveFiles fp
    let duoFiles = filter (isDuoFile . snd) files
    pure $ second filePathToModuleName <$> duoFiles
  else pure []

-- | Checks whether given filepath ends in ".duo"
isDuoFile :: FilePath -> Bool
isDuoFile fp = takeExtension fp == ".duo"


-- | Analyzes a filepath to a .duo file. Only call on arguments for which 
-- the `isDuoFile` function returns true.
-- Examples:
-- analyzeDuoFilepath "foo/bar/file.duo" = (["foo", "bar"],"file")
-- analyzeDuoFilepath "file.duo" = ([], "file")
analyzeDuoFilepath :: FilePath -> ([FilePath], String)
analyzeDuoFilepath fp =
  case splitFileName fp of
    (path, file) -> (splitDirectories path, dropExtension file)
