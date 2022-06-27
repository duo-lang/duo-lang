module Pretty.Errors (printLocatedError) where

import Control.Monad (forM_)
import Control.Monad.IO.Class
import Data.Text.IO qualified as T
import Data.List.NonEmpty qualified as NE
import Prettyprinter
import Text.Megaparsec.Pos

import Errors
import Pretty.Common
import Pretty.Constraints ()
import Pretty.Pretty
import Syntax.Common
import Utils

---------------------------------------------------------------------------------
-- Prettyprinting of Errors
---------------------------------------------------------------------------------

instance PrettyAnn ParserError where
  prettyAnn (MkParserError loc txt) = prettyAnn loc <+> prettyAnn txt

instance PrettyAnn LoweringError where
  prettyAnn MissingVarsInTypeScheme               = "Missing declaration of type variable"
  prettyAnn TopInPosPolarity                      = "Cannot use `Top` in positive polarity"
  prettyAnn BotInNegPolarity                      = "Cannot use `Bot` in negative polarity"
  prettyAnn IntersectionInPosPolarity             = "Cannot use `/\\` in positive polarity"
  prettyAnn UnionInNegPolarity                    = "Cannot use `\\/` in negative polarity"
  prettyAnn (UnknownOperator op)                  = "Undefined type operator `" <> pretty op <> "`"
  prettyAnn (XtorArityMismatch xt ar1 ar2)        = vsep [ "Arity mismatch:"
                                                   , "  Constructor/Destructor:" <+> prettyAnn xt
                                                   , "  Specified Arity:" <+> pretty ar1
                                                   , "  Used Arity:" <+> pretty ar2
                                                   ]
  prettyAnn (UndefinedPrimOp (pt, op))             = "Undefined primitive operator  " <> prettyAnn (primOpKeyword op ++ primTypeKeyword pt)
  prettyAnn (PrimOpArityMismatch (pt, op) ar1 ar2) = vsep [ "Arity mismatch:"
                                                   , "  Primitive operation:" <+> prettyAnn (primOpKeyword op ++ primTypeKeyword pt)
                                                   , "  Specified Arity:" <+> pretty ar1
                                                   , "  Used Arity:" <+> pretty ar2
                                                   ]
  prettyAnn (CmdExpected t)                        = "Command expected: " <+> pretty t
  prettyAnn (InvalidStar t)                        = "Invalid Star: " <+> pretty t

instance PrettyAnn Error where
  prettyAnn (ParserErrorBundle errs)        = vsep (NE.toList (prettyAnn <$> errs))
  prettyAnn (EvalError loc err)             = prettyMaybeLoc loc <>"Evaluation error:" <+> pretty err
  prettyAnn (GenConstraintsError loc err)   = prettyMaybeLoc loc <> "Constraint generation error:" <+> pretty err
  prettyAnn (SolveConstraintsError loc err) = prettyMaybeLoc loc <> "Constraint solving error:" <+> pretty err
  prettyAnn (TypeAutomatonError loc err)    = prettyMaybeLoc loc <> "Type simplification error:" <+> pretty err
  prettyAnn (LowerError loc err)            = prettyMaybeLoc loc <> prettyAnn err
  prettyAnn (OtherError loc err)            = prettyMaybeLoc loc <> "Other Error:" <+> pretty err
  prettyAnn (NoImplicitArg loc err)         = prettyMaybeLoc loc <> "No implicit arg: " <+> pretty err
---------------------------------------------------------------------------------
-- Prettyprinting a region from a source file
---------------------------------------------------------------------------------

printLocatedError :: MonadIO m => Error -> m ()
printLocatedError err@(getLoc -> Nothing) = liftIO $ T.putStrLn (ppPrint err)
printLocatedError err@(getLoc -> Just loc) = liftIO $ do
  T.putStrLn ("Error at: " <> ppPrint loc)
  printRegion loc
  T.putStrLn ""
  T.putStrLn (ppPrint err)
printLocatedError _ = error "unreachable: Satisfy the pattern match checker :/"

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
