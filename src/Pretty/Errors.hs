module Pretty.Errors
  ( printLocatedReport
  ) where

import Control.Monad.IO.Class ( MonadIO(..) )
import Data.Text (Text)
import Error.Diagnose
    ( stdout,
      addReport,
      printDiagnostic,
      err,
      warn,
      defaultStyle,
      def,
      Report )
import Prettyprinter


import Errors
import Pretty.Constraints ()
import Pretty.Pretty ( PrettyAnn(..) )
import Syntax.Common.Primitives ( primTypeKeyword, primOpKeyword )

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

class ToReport a where
  toReport :: a -> Report Text

instance ToReport LoweringError where
  toReport MissingVarsInTypeScheme     = err Nothing "" [] []
  toReport TopInPosPolarity            = err Nothing "" [] []
  toReport BotInNegPolarity            = err Nothing "" [] []
  toReport IntersectionInPosPolarity   = err Nothing "" [] []
  toReport UnionInNegPolarity          = err Nothing "" [] []
  toReport (UnknownOperator _op)       = err Nothing "" [] []
  toReport XtorArityMismatch {}        = err Nothing "" [] []
  toReport (UndefinedPrimOp  _)        = err Nothing "" [] []
  toReport PrimOpArityMismatch {}      = err Nothing "" [] []
  toReport (CmdExpected _)             = err Nothing "" [] []
  toReport (InvalidStar _)             = err Nothing "" [] []

instance ToReport Error where
  toReport (ParserError _loc msg)           = err Nothing msg [] []
  toReport (EvalError _loc msg)             = err Nothing msg [] []
  toReport (GenConstraintsError _loc msg)   = err Nothing msg [] []
  toReport (SolveConstraintsError _loc msg) = err Nothing msg [] []
  toReport (TypeAutomatonError _loc msg)    = err Nothing msg [] []
  toReport (LowerError _loc err)            = toReport err
  toReport (OtherError _loc msg)            = err Nothing msg [] []
  toReport (NoImplicitArg _loc msg)         = err Nothing msg [] []

---------------------------------------------------------------------------------
-- Prettyprinting a region from a source file
---------------------------------------------------------------------------------

printLocatedReport :: (ToReport r, MonadIO m) => r -> m ()
printLocatedReport r = liftIO $ do
  let report = toReport r
  let diag = addReport def report
  printDiagnostic stdout True True 4 defaultStyle diag

---------------------------------------------------------------------------------
-- Turning warnings into reports
---------------------------------------------------------------------------------

instance ToReport Warning where
  toReport (Warning _loc msg) = warn Nothing msg [] []

instance PrettyAnn Warning where
  prettyAnn (Warning loc txt) = "Warning:" <+> prettyAnn loc <+> prettyAnn txt

