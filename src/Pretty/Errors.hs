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
      Report, Marker (This), Position (..), addFile, Note (Hint) )
import Prettyprinter


import Errors
import Pretty.Constraints ()
import Pretty.Terms ()
import Pretty.Pretty ( PrettyAnn(..), ppPrint )
import Loc (Loc (Loc), HasLoc (getLoc))
import Text.Megaparsec (SourcePos(..), unPos)
import System.Directory (doesFileExist)
import Syntax.CST.Types (PrdCns(..))


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
  prettyAnn (MethodArityMismatch loc mn cn ar1 ar2) =
    vsep  [ prettyAnn loc
          , "Arity mismatch:"
          , "  Type class method:" <+> prettyAnn mn <+> "from class:" <+> prettyAnn cn
          , "  Specified Arity:" <+> pretty ar1
          , "  Used Arity:" <+> pretty ar2
          ]
  prettyAnn (PrimOpArityMismatch loc op ar1) =
    vsep [ prettyAnn loc
         , "Arity mismatch:"
         , "  Primitive operation:" <+> prettyAnn op
         , "  Used Arity:" <+> pretty ar1
         ]
  prettyAnn (CmdExpected loc t) =
    prettyAnn loc <+> "Command expected: " <+> pretty t
  prettyAnn (InvalidStar loc t) =
    prettyAnn loc <+> "Invalid Star: " <+> pretty t

instance PrettyAnn ConstraintGenerationError where
  prettyAnn (BoundVariableOutOfBounds loc rep (i,j)) =
    vsep [ prettyAnn loc
         , "Bound Variable out of bounds:"
         , "PrdCns:" <+> pretty (show rep)
         , "Index:" <+> pretty (show (i,j))
         ]
  prettyAnn (BoundVariableWrongMode loc Prd (i,j)) = 
    vsep [ prettyAnn loc
         , "Bound Variable" <+> pretty (show (i,j)) <+> "was expected to be PrdType, but CnsType was found."
         ]
  prettyAnn (BoundVariableWrongMode loc Cns (i,j)) = 
    vsep [ prettyAnn loc
         , "Bound Variable" <+> pretty (show (i,j)) <+> "was expected to be CnsType, but PrdType was found."
         ]
  prettyAnn (PatternMatchMissingXtor loc xn tn) =
    vsep [ prettyAnn loc
         , "Pattern Match Exhaustiveness Error. Xtor:" <+> prettyAnn xn <+> "of type" <+> prettyAnn tn <+> "is not matched against."
         ]
    
  prettyAnn (PatternMatchAdditional loc xn tn) =
    vsep [ prettyAnn loc
         , "Pattern Match Error. The xtor" <+> prettyAnn xn <+> "does not occur in the declaration of type" <+> prettyAnn tn
         ]
  prettyAnn (InstanceImplementationMissing loc m) =
    vsep [ prettyAnn loc
         , "Instance Declaration Error. Method: " <> prettyAnn m <> " is declared but not implemented."
         ]
  prettyAnn (InstanceImplementationAdditional loc m) =
    vsep [ prettyAnn loc
         , "Instance Declaration Error. Method: " <> prettyAnn m <> " is implemented but not declared."
         ]
  prettyAnn (EmptyNominalMatch loc) =
    vsep [ prettyAnn loc
         , "Unreachable: A nominal match needs to have at least one case."
         ]
  prettyAnn (EmptyRefinementMatch loc) =
    vsep [ prettyAnn loc
         , "Unreachable: A refinement match needs to have at least one case."
         ]
  prettyAnn (LinearContextsUnequalLength loc info ctx1 ctx2) =
    vsep [ prettyAnn loc
         , "genConstraintsCtxts: Linear contexts have unequal length"
         , "Constraint Info: " <> prettyAnn info
         , "Pos context: " <> prettyAnn ctx1
         , "Neg context: " <> prettyAnn ctx2
         ]
  prettyAnn (LinearContextIncompatibleTypeMode loc Prd info) =
    vsep [ prettyAnn loc
         , "genConstraintsCtxts: Tried to constrain PrdType by CnsType"
         , "Constraint Info:" <+> prettyAnn info
         ]
  prettyAnn (LinearContextIncompatibleTypeMode loc Cns info) =
    vsep [ prettyAnn loc
         , "genConstraintsCtxts: Tried to constrain CnsType by PrdType"
         , "Constraint Info:" <+> prettyAnn info
         ]
    

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
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(TopInPosPolarity loc) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(BotInNegPolarity loc) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(IntersectionInPosPolarity loc) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(UnionInNegPolarity loc) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(UnknownOperator loc _op) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(XtorArityMismatch loc _ _ _) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(MethodArityMismatch loc _ _ _ _) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(PrimOpArityMismatch loc _ _) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(CmdExpected loc _) = 
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(InvalidStar loc _) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []

instance ToReport ConstraintGenerationError where
  toReport e@(BoundVariableOutOfBounds loc _ _) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(BoundVariableWrongMode loc _ _) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(PatternMatchMissingXtor loc _ _) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(PatternMatchAdditional loc _ _) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(InstanceImplementationMissing loc _) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(InstanceImplementationAdditional loc _) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(EmptyNominalMatch loc) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(EmptyRefinementMatch loc) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(LinearContextsUnequalLength loc _ _ _) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []
  toReport e@(LinearContextIncompatibleTypeMode loc _ _) =
    err (Just "E-000") (ppPrint e) [(toDiagnosePosition loc, This "Location of the error")] []

instance ToReport ConstraintSolverError where
  toReport (SomeConstraintSolverError loc msg) =
    err (Just "E-000") msg [(toDiagnosePosition loc, This "Location of the error")] []

instance ToReport TypeAutomatonError where
  toReport (SomeTypeAutomatonError loc msg) =
    err (Just "E-000") msg [(toDiagnosePosition loc, This "Location of the error")] []

instance ToReport EvalError where
  toReport (SomeEvalError loc msg) =
    err (Just "E-000") msg [(toDiagnosePosition loc, This "Location of the error")] []

instance ToReport OtherError where
  toReport (SomeOtherError loc msg) =
    err (Just "E-000") msg [(toDiagnosePosition loc, This "Location of the error")] []

instance ToReport ParserError where
  toReport (SomeParserError loc msg) =
    err (Just "E-000") msg [(toDiagnosePosition loc, This "Location of the error")] []

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

printLocatedReport :: (ToReport r, HasLoc r, MonadIO m) => r -> m ()
printLocatedReport r = liftIO $ do
  let report = toReport r
  let diag = addReport def report
  let (Loc (SourcePos fp _ _) _) = getLoc r
  fileExists <- doesFileExist fp
  if not fileExists
    then printDiagnostic stdout True True 4 defaultStyle diag
    else do
      fileContent <- readFile fp
      let diag' = addFile diag fp fileContent
      printDiagnostic stdout True True 4 defaultStyle diag'

---------------------------------------------------------------------------------
-- Turning warnings into reports
---------------------------------------------------------------------------------

instance ToReport Warning where
  toReport w@(MisnamedProducerVar loc _var) =
    let
        msg = ppPrint w
        hint = Hint "Rename the variable so that it doesn't start with the letter \"k\"."
        poshint = (toDiagnosePosition loc, This "producer variable")
    in
      warn (Just "W-000") msg [poshint] [hint]
  toReport w@(MisnamedConsumerVar loc _var) =
    let
        msg = ppPrint w
        hint = Hint "Rename the variable so that it starts with the letter \"k\"."
        poshint = (toDiagnosePosition loc, This "consumer variable")
    in
      warn (Just "W-000") msg [poshint] [hint]

instance PrettyAnn Warning where
  prettyAnn (MisnamedProducerVar _ var) =
    "Producer variable" <+> pretty var <+> "should not start with letter \"k\"."
  prettyAnn (MisnamedConsumerVar _ var) =
    "Consumer variable" <+> pretty var <+> "should start with letter \"k\"."

