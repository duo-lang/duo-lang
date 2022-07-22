module Pretty.Errors (printLocatedError) where

import Control.Monad (forM_)
import Control.Monad.IO.Class
import Data.Text.IO qualified as T
import Data.Text (Text)
import Error.Diagnose
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
  prettyAnn (ParserError loc msg)           = prettyAnn loc <> "Parser error:" <+> pretty msg
  prettyAnn (EvalError loc err)             = prettyAnn loc <> "Evaluation error:" <+> pretty err
  prettyAnn (GenConstraintsError loc err)   = prettyAnn loc <> "Constraint generation error:" <+> pretty err
  prettyAnn (SolveConstraintsError loc err) = prettyAnn loc <> "Constraint solving error:" <+> pretty err
  prettyAnn (TypeAutomatonError loc err)    = prettyAnn loc <> "Type simplification error:" <+> pretty err
  prettyAnn (LowerError loc err)            = prettyAnn loc <> prettyAnn err
  prettyAnn (OtherError loc err)            = prettyAnn loc <> "Other Error:" <+> pretty err
  prettyAnn (NoImplicitArg loc err)         = prettyAnn loc <> "No implicit arg: " <+> pretty err

---------------------------------------------------------------------------------
-- Turning an error into a report
---------------------------------------------------------------------------------

loweringErrorToReport :: LoweringError -> Report Text
loweringErrorToReport MissingVarsInTypeScheme     = err Nothing "" [] []
loweringErrorToReport TopInPosPolarity            = err Nothing "" [] []
loweringErrorToReport BotInNegPolarity            = err Nothing "" [] []
loweringErrorToReport IntersectionInPosPolarity   = err Nothing "" [] []
loweringErrorToReport UnionInNegPolarity          = err Nothing "" [] []
loweringErrorToReport (UnknownOperator _op)       = err Nothing "" [] []
loweringErrorToReport XtorArityMismatch {}        = err Nothing "" [] []
loweringErrorToReport (UndefinedPrimOp  _)        = err Nothing "" [] []
loweringErrorToReport PrimOpArityMismatch {}      = err Nothing "" [] []
loweringErrorToReport (CmdExpected _)             = err Nothing "" [] []
loweringErrorToReport (InvalidStar _)             = err Nothing "" [] []

errorToReport :: Error -> Report Text
errorToReport (ParserError _loc msg)           = err Nothing msg [] []
errorToReport (EvalError _loc msg)             = err Nothing msg [] []
errorToReport (GenConstraintsError _loc msg)   = err Nothing msg [] []
errorToReport (SolveConstraintsError _loc msg) = err Nothing msg [] []
errorToReport (TypeAutomatonError _loc msg)    = err Nothing msg [] []
errorToReport (LowerError _loc err)            = loweringErrorToReport err
errorToReport (OtherError _loc msg)            = err Nothing msg [] []
errorToReport (NoImplicitArg _loc msg)         = err Nothing msg [] []

---------------------------------------------------------------------------------
-- Prettyprinting a region from a source file
---------------------------------------------------------------------------------

printLocatedError :: MonadIO m => Error -> m ()
printLocatedError err = liftIO $ do
  let report = errorToReport err
  let diag = addReport def report
  printDiagnostic stdout True True 4 defaultStyle diag

instance PrettyAnn Warning where
  prettyAnn (Warning loc txt) = "Warning:" <+> prettyAnn loc <+> prettyAnn txt
