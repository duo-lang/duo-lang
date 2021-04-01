{-# LANGUAGE OverloadedStrings #-}
module Pretty.Errors where

import Control.Monad (forM_)
import Prettyprinter
import Text.Megaparsec.Pos


import Pretty.Pretty
import Utils

---------------------------------------------------------------------------------
-- Prettyprinting of Errors
---------------------------------------------------------------------------------

instance PrettyAnn Error where
  prettyAnn (ParseError err) = "Parsing error:" <+> pretty err
  prettyAnn (EvalError err) = "Evaluation error:" <+> pretty err
  prettyAnn (GenConstraintsError err) = "Constraint generation error:" <+> pretty err
  prettyAnn (SolveConstraintsError err) = "Constraint solving error:" <+> pretty err
  prettyAnn (TypeAutomatonError err) = "Type simplification error:" <+> pretty err
  prettyAnn (OtherError err) = "Other Error:" <+> pretty err

instance PrettyAnn Pos where
  prettyAnn p = pretty (unPos p)

instance PrettyAnn Loc where
  prettyAnn (Loc (SourcePos fp line1 column1) (SourcePos _ line2 column2)) =
    pretty fp <> ":" <> prettyAnn line1 <> ":" <> prettyAnn column1 <> "-" <> prettyAnn line2 <> ":" <> prettyAnn column2

---------------------------------------------------------------------------------
-- Prettyprinting a region from a source file
---------------------------------------------------------------------------------

printLocatedError :: LocatedError -> IO ()
printLocatedError (Located loc err) = do
  putStrLn ("Error at: " ++ ppPrint loc)
  putStrLn ""
  printRegion loc
  putStrLn ""
  putStrLn (ppPrint err)

printRegion :: Loc -> IO ()
printRegion (Loc (SourcePos fp line1 _) (SourcePos _ line2 _)) = do
  file <- readFile fp
  let region = getRegion file (unPos line1) (unPos line2)
  let annotatedRegion = generatePrefixes region
  forM_ annotatedRegion $ \line -> putStrLn line


getRegion :: String -> Int -> Int -> [(Int, String)]
getRegion str start end = take (end - (start - 1)) . drop (start - 1) $ zip [1..] (lines str)

generatePrefixes :: [(Int, String)] -> [String]
generatePrefixes lines = foo <$> lines
  where
    foo (line, content) = show line ++ " | " ++ content



