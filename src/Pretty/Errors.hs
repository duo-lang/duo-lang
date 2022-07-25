module Pretty.Errors (printLocatedError) where

import Control.Monad (forM_)
import Control.Monad.IO.Class
import Data.Text.IO qualified as T
import Prettyprinter
import Text.Megaparsec.Pos

import Errors
import Pretty.Constraints ()
import Pretty.Pretty
import Syntax.Common
import Utils

---------------------------------------------------------------------------------
-- Prettyprinting of Errors
---------------------------------------------------------------------------------

instance PrettyAnn ResolutionError where
  prettyAnn (MissingVarsInTypeScheme loc) =
    prettyAnn loc <+> "Missing declaration of type variable"
  prettyAnn (TopInPosPolarity loc) =
    prettyAnn loc <+> "Cannot use `Top` in positive polarity"
  prettyAnn (BotInNegPolarity loc) = 
    prettyAnn loc <+> "Cannot use `Bot` in negative polarity"
  prettyAnn (IntersectionInPosPolarity loc) =
    prettyAnn loc <+> "Cannot use `/\\` in positive polarity"
  prettyAnn (UnionInNegPolarity loc) = 
    prettyAnn loc <+> "Cannot use `\\/` in negative polarity"
  prettyAnn (UnknownOperator loc op) =
    prettyAnn loc <+> "Undefined type operator `" <> pretty op <> "`"
  prettyAnn (XtorArityMismatch loc xt ar1 ar2) =
    vsep [ prettyAnn loc
         , "Arity mismatch:"
         , "  Constructor/Destructor:" <+> prettyAnn xt
         , "  Specified Arity:" <+> pretty ar1
         , "  Used Arity:" <+> pretty ar2
         ]
  prettyAnn (UndefinedPrimOp loc (pt, op)) = 
    prettyAnn loc <+> "Undefined primitive operator" <+> prettyAnn (primOpKeyword op ++ primTypeKeyword pt)
  prettyAnn (PrimOpArityMismatch loc (pt, op) ar1 ar2) =
    vsep [ prettyAnn loc
         , "Arity mismatch:"
         , "  Primitive operation:" <+> prettyAnn (primOpKeyword op ++ primTypeKeyword pt)
         , "  Specified Arity:" <+> pretty ar1
         , "  Used Arity:" <+> pretty ar2
         ]
  prettyAnn (CmdExpected loc t) =
    prettyAnn loc <+> "Command expected: " <+> pretty t
  prettyAnn (InvalidStar loc t) =
    prettyAnn loc <+> "Invalid Star: " <+> pretty t

instance PrettyAnn ConstraintGenerationError where
  prettyAnn (SomeConstraintGenerationError loc msg) =
    prettyAnn loc <> "Constraint generation error:" <+> pretty msg

instance PrettyAnn ConstraintSolverError where
  prettyAnn (SomeConstraintSolverError loc msg) =
    prettyAnn loc <> "Constraint solver error:" <+> pretty msg

instance PrettyAnn TypeAutomatonError where
  prettyAnn (SomeTypeAutomatonError loc msg) =
    prettyAnn loc <> "Type automaton error:" <+> pretty msg

instance PrettyAnn EvalError where
  prettyAnn (SomeEvalError loc msg) =
    prettyAnn loc <> "Evaluation error:" <+> pretty msg

instance PrettyAnn Error where
  prettyAnn (ErrConstraintGeneration err)   = prettyAnn err
  prettyAnn (ErrResolution err)             = prettyAnn err
  prettyAnn (ErrConstraintSolver err)       = prettyAnn err
  prettyAnn (ErrTypeAutomaton err)          = prettyAnn err
  prettyAnn (ErrEval err)                   = prettyAnn err
  --
  prettyAnn (ParserError loc msg)           = prettyAnn loc <> "Parser error:" <+> pretty msg
  prettyAnn (OtherError loc err)            = prettyAnn loc <> "Other Error:" <+> pretty err

---------------------------------------------------------------------------------
-- Prettyprinting a region from a source file
---------------------------------------------------------------------------------

printLocatedError :: MonadIO m => Error -> m ()
printLocatedError err = liftIO $ do
  let loc = getLoc err
  T.putStrLn ("Error at: " <> ppPrint loc)
  printRegion loc
  T.putStrLn ""
  T.putStrLn (ppPrint err)

printRegion :: Loc -> IO ()
printRegion (Loc (SourcePos "<interactive>" _ _) SourcePos {}) = return ()
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


instance PrettyAnn Warning where
  prettyAnn (Warning loc txt) = "Warning:" <+> prettyAnn loc <+> prettyAnn txt
