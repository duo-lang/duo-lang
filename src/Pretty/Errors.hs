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
      Report, Marker (This), Position (..) )
import Prettyprinter


import Errors
import Pretty.Constraints ()
import Pretty.Pretty ( PrettyAnn(..), ppPrint )
import Syntax.Common.Primitives ( primTypeKeyword, primOpKeyword )
import Utils (Loc (Loc))
import Text.Megaparsec (SourcePos(..), unPos)

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

instance PrettyAnn OtherError where
  prettyAnn (SomeOtherError loc msg) =
    prettyAnn loc <> "Other error:" <+> pretty msg

instance PrettyAnn ParserError where
  prettyAnn (SomeParserError loc msg) =
    prettyAnn loc <> "Parser error:" <+> pretty msg

instance PrettyAnn Error where
  prettyAnn (ErrConstraintGeneration err)   = prettyAnn err
  prettyAnn (ErrResolution err)             = prettyAnn err
  prettyAnn (ErrConstraintSolver err)       = prettyAnn err
  prettyAnn (ErrTypeAutomaton err)          = prettyAnn err
  prettyAnn (ErrEval err)                   = prettyAnn err
  prettyAnn (ErrOther err)                  = prettyAnn err
  prettyAnn (ErrParser err)                 = prettyAnn err

---------------------------------------------------------------------------------
-- Turning an error into a report
---------------------------------------------------------------------------------

class ToReport a where
  toReport :: a -> Report Text

toDiagnosePosition :: Loc -> Position
toDiagnosePosition (Loc (SourcePos fp p1 p2) (SourcePos _ p3 p4)) =
  Position { begin = (unPos p1,unPos p2)
           , end = (unPos p3, unPos p4)
           , file = fp
           }

instance ToReport ResolutionError where
  toReport e@(MissingVarsInTypeScheme loc) =
    err Nothing (ppPrint e) [(toDiagnosePosition loc, This "")] []
  toReport e@(TopInPosPolarity loc) =
    err Nothing (ppPrint e) [(toDiagnosePosition loc, This "")] []
  toReport e@(BotInNegPolarity loc) =
    err Nothing (ppPrint e) [(toDiagnosePosition loc, This "")] []
  toReport e@(IntersectionInPosPolarity loc) =
    err Nothing (ppPrint e) [(toDiagnosePosition loc, This "")] []
  toReport e@(UnionInNegPolarity loc) =
    err Nothing (ppPrint e) [(toDiagnosePosition loc, This "")] []
  toReport e@(UnknownOperator loc _op) =
    err Nothing (ppPrint e) [(toDiagnosePosition loc, This "")] []
  toReport e@(XtorArityMismatch loc _ _ _) =
    err Nothing (ppPrint e) [(toDiagnosePosition loc, This "")] []
  toReport e@(UndefinedPrimOp loc _) =
    err Nothing (ppPrint e) [(toDiagnosePosition loc, This "")] []
  toReport e@(PrimOpArityMismatch loc _ _ _) =
    err Nothing (ppPrint e) [(toDiagnosePosition loc, This "")] []
  toReport e@(CmdExpected loc _) = 
    err Nothing (ppPrint e) [(toDiagnosePosition loc, This "")] []
  toReport e@(InvalidStar loc _) =
    err Nothing (ppPrint e) [(toDiagnosePosition loc, This "")] []

instance ToReport ConstraintGenerationError where
  toReport (SomeConstraintGenerationError loc msg) =
    err Nothing msg [(toDiagnosePosition loc, This "")] []

instance ToReport ConstraintSolverError where
  toReport (SomeConstraintSolverError loc msg) =
    err Nothing msg [(toDiagnosePosition loc, This "")] []

instance ToReport TypeAutomatonError where
  toReport (SomeTypeAutomatonError loc msg) =
    err Nothing msg [(toDiagnosePosition loc, This "")] []

instance ToReport EvalError where
  toReport (SomeEvalError loc msg) =
    err Nothing msg [(toDiagnosePosition loc, This "")] []

instance ToReport OtherError where
  toReport (SomeOtherError loc msg) =
    err Nothing msg [(toDiagnosePosition loc, This "")] []

instance ToReport ParserError where
  toReport (SomeParserError loc msg) =
    err Nothing msg [(toDiagnosePosition loc, This "")] []

instance ToReport Error where
  toReport (ErrConstraintGeneration err) = toReport err
  toReport (ErrResolution err)           = toReport err
  toReport (ErrConstraintSolver err)     = toReport err
  toReport (ErrTypeAutomaton err)        = toReport err
  toReport (ErrEval err)                 = toReport err
  toReport (ErrOther err)                = toReport err
  toReport (ErrParser err)               = toReport err

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

