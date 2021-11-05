module Pretty.Errors (printLocatedError) where

import Control.Monad (forM_)
import Control.Monad.IO.Class
import Data.Text.IO qualified as T
import Prettyprinter
import Text.Megaparsec.Pos

import Pretty.Pretty
import Pretty.Constraints ()
import Utils
import Errors

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

instance PrettyAnn LocatedError where
  prettyAnn (Located _ err) = prettyAnn err

---------------------------------------------------------------------------------
-- Prettyprinting a region from a source file
---------------------------------------------------------------------------------

printLocatedError :: MonadIO m => LocatedError -> m ()
printLocatedError (Located loc err) = liftIO $ do
  T.putStrLn ("Error at: " <> ppPrint loc)
  printRegion loc
  T.putStrLn ""
  T.putStrLn (ppPrint err)

printRegion :: Loc -> IO ()
printRegion (Loc (SourcePos "<interactive>" _ _) (SourcePos _ _ _)) = return ()
printRegion (Loc (SourcePos fp line1 _) (SourcePos _ line2 _)) = do
  T.putStrLn ""
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



