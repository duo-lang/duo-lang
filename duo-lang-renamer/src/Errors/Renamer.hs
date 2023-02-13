module Errors.Renamer where

import Loc
import Data.Text
import Syntax.CST.Names
import Syntax.CST.Types

----------------------------------------------------------------------------------
-- Errors emitted during the resolution phase
----------------------------------------------------------------------------------

data ResolutionError where
  -- Type scheme violations
  MissingVarsInTypeScheme :: Loc -> ResolutionError
  -- Polarity violations
  TopInPosPolarity :: Loc -> ResolutionError
  BotInNegPolarity :: Loc -> ResolutionError
  IntersectionInPosPolarity :: Loc -> ResolutionError
  UnionInNegPolarity :: Loc -> ResolutionError
  -- Operator errors
  MethodArityMismatch :: Loc
                      -> MethodName
                      -> ClassName
                      -> Int
                      -> Int
                      -> ResolutionError
  XtorArityMismatch :: Loc
                    -> XtorName
                    -> Int
                    -> Int
                    -> ResolutionError
  PrimOpArityMismatch :: Loc
                      -> PrimName
                      -> Int
                      -> ResolutionError
  CmdExpected :: Loc -> Text -> ResolutionError
  InvalidStar  :: Loc -> Text -> ResolutionError
  -- Already In Use
  TypeNameAlreadyUsed :: Loc -> TypeName -> ResolutionError
  XtorNameAlreadyUsed :: Loc -> XtorName -> ResolutionError
  FreeVarNameAlreadyUsed :: Loc -> FreeVarName -> ResolutionError
  TyOpAlreadyUsed :: Loc -> TyOpName -> ResolutionError
  OrphanInstance :: Loc -> FreeVarName -> ClassName -> Typ -> ResolutionError
  -- Not Found in SymbolTable
  XtorNotFound :: Loc -> XtorName -> ResolutionError
  XtorAmbiguous :: Loc -> XtorName -> ResolutionError
  TypeNameNotFound :: Loc -> TypeName -> ResolutionError
  TypeNameAmbiguous :: Loc -> TypeName -> ResolutionError
  TypeOperatorNotFound :: Loc -> TyOpName -> ResolutionError
  TypeOperatorAmbiguous :: Loc -> TyOpName -> ResolutionError
  -- Other
  UnknownResolutionError :: Loc -> Text -> ResolutionError

deriving instance Show ResolutionError

instance HasLoc ResolutionError where
  getLoc :: ResolutionError -> Loc
  getLoc (MissingVarsInTypeScheme loc) = loc
  getLoc (TopInPosPolarity loc) = loc
  getLoc (BotInNegPolarity loc) = loc
  getLoc (IntersectionInPosPolarity loc) = loc
  getLoc (UnionInNegPolarity loc) = loc
  getLoc (MethodArityMismatch loc _ _ _ _) = loc
  getLoc (XtorArityMismatch loc _ _ _) = loc
  getLoc (PrimOpArityMismatch loc _ _) = loc
  getLoc (CmdExpected loc _) = loc
  getLoc (InvalidStar loc _) = loc
  getLoc (TypeNameAlreadyUsed loc _) = loc
  getLoc (TypeNameNotFound loc _) = loc
  getLoc (TypeNameAmbiguous loc _) = loc
  getLoc (TyOpAlreadyUsed loc _) = loc
  getLoc (XtorNameAlreadyUsed loc _) = loc
  getLoc (XtorNotFound loc _) = loc
  getLoc (XtorAmbiguous loc _) = loc
  getLoc (OrphanInstance loc _ _ _) = loc
  getLoc (TypeOperatorNotFound loc _) = loc
  getLoc (TypeOperatorAmbiguous loc _) = loc
  getLoc (FreeVarNameAlreadyUsed loc _) = loc
  getLoc (UnknownResolutionError loc _) = loc


instance AttachLoc ResolutionError where
  attachLoc :: Loc -> ResolutionError -> ResolutionError
  attachLoc loc (MissingVarsInTypeScheme _) = MissingVarsInTypeScheme loc
  attachLoc loc (TopInPosPolarity _) = TopInPosPolarity loc
  attachLoc loc (BotInNegPolarity _) = BotInNegPolarity loc
  attachLoc loc (IntersectionInPosPolarity _) = IntersectionInPosPolarity loc
  attachLoc loc (UnionInNegPolarity _) = UnionInNegPolarity loc
  attachLoc loc (XtorArityMismatch _ xt i1 i2) = XtorArityMismatch loc xt i1 i2
  attachLoc loc (MethodArityMismatch _ mt ct i1 i2) = MethodArityMismatch loc mt ct i1 i2
  attachLoc loc (PrimOpArityMismatch _ po i) = PrimOpArityMismatch loc po i
  attachLoc loc (CmdExpected _ t) = CmdExpected loc t
  attachLoc loc (InvalidStar _ t) = InvalidStar loc t
  attachLoc loc (TypeNameAlreadyUsed _ tn) = TypeNameAlreadyUsed loc tn
  attachLoc loc (TypeNameNotFound _ tn) = TypeNameNotFound loc tn
  attachLoc loc (TypeNameAmbiguous _ tn) = TypeNameAmbiguous loc tn
  attachLoc loc (TyOpAlreadyUsed _ op) = TyOpAlreadyUsed loc op
  attachLoc loc (XtorNameAlreadyUsed _ xt) = XtorNameAlreadyUsed loc xt
  attachLoc loc (XtorNotFound _ xt) = XtorNotFound loc xt
  attachLoc loc (XtorAmbiguous _ xt) = XtorAmbiguous loc xt
  attachLoc loc (OrphanInstance _ isn cn ty) = OrphanInstance loc isn cn ty
  attachLoc loc (TypeOperatorNotFound _ op) = TypeOperatorNotFound loc op
  attachLoc loc (TypeOperatorAmbiguous _ op) = TypeOperatorAmbiguous loc op
  attachLoc loc (FreeVarNameAlreadyUsed _ fv) = FreeVarNameAlreadyUsed loc fv
  attachLoc loc (UnknownResolutionError _ msg) = UnknownResolutionError loc msg


---------------------------------------------------------------------------------------------
-- Warnings
---------------------------------------------------------------------------------------------

data Warning where
  -- | Warning for producer that starts with the letter "k".
  MisnamedProducerVar :: Loc -> Text -> Warning
  -- | Warning for consumer that doesn't start with the letter "k".
  MisnamedConsumerVar :: Loc -> Text -> Warning

deriving instance Show Warning

instance HasLoc Warning where
  getLoc (MisnamedProducerVar loc _) = loc
  getLoc (MisnamedConsumerVar loc _) = loc

instance AttachLoc Warning where
  attachLoc loc (MisnamedProducerVar _ msg) = MisnamedProducerVar loc msg
  attachLoc loc (MisnamedConsumerVar _ msg) = MisnamedConsumerVar loc msg