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
  , isDuoFile
  , analyzeDuoFilepath
  , filePathToModuleName
  , moduleNameToFilePath
  , moduleNameToFullPath
  , listRecursiveDuoFiles
  , isModuleFile
  , sequenceMap) where

import Data.Char (isSpace)
import Data.Foldable (foldl')
import Data.List.NonEmpty (NonEmpty(..))
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import Data.Set qualified as S
import Data.Text (Text)
import Data.Text qualified as T
import System.FilePath (takeExtension, splitFileName, splitDirectories, dropExtension, takeBaseName, (</>), joinPath, (<.>), takeFileName, makeRelative)
import Syntax.CST.Names (ModuleName (..))
import System.Directory (doesFileExist, doesDirectoryExist, listDirectory)
import Control.Monad (forM)

----------------------------------------------------------------------------------
-- Helper Functions
----------------------------------------------------------------------------------

sequenceMap :: forall k a. Map k (Maybe a) -> Maybe (Map k a) 
sequenceMap = M.traverseWithKey (const id) 

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

moduleNameToFilePath :: ModuleName -> FilePath
moduleNameToFilePath mn =
  let filename = T.unpack mn.mn_base <.> "duo"
  in joinPath $ (T.unpack <$> mn.mn_path) ++ [filename]

moduleNameToFullPath :: ModuleName -> FilePath -> FilePath
moduleNameToFullPath mn fp =
  let relPath = moduleNameToFilePath mn
  in fp </> relPath

isModuleFile :: ModuleName -> FilePath -> IO Bool
isModuleFile mn fp = doesFileExist (moduleNameToFullPath mn fp)

-- | Checks whether given filepath ends in ".duo"
isDuoFile :: FilePath -> Bool
isDuoFile fp = takeExtension fp == ".duo"

isHidden :: FilePath -> Bool
isHidden [] = False
isHidden (c:_) = c == '.'

listRecursiveFiles :: FilePath -> IO [FilePath]
listRecursiveFiles topdir = do
  names <- listDirectory topdir
  let names' = filter (not. isHidden) names
  paths <- forM names' $ \name -> do
    let path = topdir </> name
    isDirectory <- doesDirectoryExist path
    if isDirectory
      then listRecursiveFiles path
      else if isDuoFile path && not (isHidden $ takeFileName path)
            then pure [path]
            else pure []
  pure (concat paths)


listRecursiveDuoFiles :: FilePath -> IO [ModuleName]
listRecursiveDuoFiles fp = do
  exists <- doesDirectoryExist fp
  if exists
  then do
    files <- listRecursiveFiles fp
    pure $ map (filePathToModuleName . makeRelative fp) files
  else pure []

-- | Analyzes a filepath to a .duo file. Only call on arguments for which 
-- the `isDuoFile` function returns true.
-- Examples:
-- analyzeDuoFilepath "foo/bar/file.duo" = (["foo", "bar"],"file")
-- analyzeDuoFilepath "file.duo" = ([], "file")
analyzeDuoFilepath :: FilePath -> ([FilePath], String)
analyzeDuoFilepath fp =
  case splitFileName fp of
    (path, file) -> (splitDirectories path, dropExtension file)
