module Syntax.CST.Program where

import Data.Text (Text)

import Syntax.CST.Terms
import Syntax.Common.TypesUnpol
import Syntax.Common
import Utils

---------------------------------------------------------------------------------
-- Producer / Consumer Declaration
---------------------------------------------------------------------------------

-- | A toplevel producer or consumer declaration.
data PrdCnsDeclaration = MkPrdCnsDeclaration
  { pcdecl_loc :: Loc
    -- ^ The source code location of the declaration.
  , pcdecl_doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , pcdecl_pc :: PrdCns
    -- ^ Whether a producer or consumer is declared.
  , pcdecl_isRec :: IsRec
    -- ^ Whether the declaration can refer to itself recursively.
  , pcdecl_name :: FreeVarName
    -- ^ The name of the producer / consumer.
  , pcdecl_annot :: Maybe TypeScheme
    -- ^ The type signature.
  , pcdecl_term :: Term
    -- ^ The term itself.
}

deriving instance (Show PrdCnsDeclaration)

---------------------------------------------------------------------------------
-- Command Declaration
---------------------------------------------------------------------------------

-- | A toplevel command declaration.
data CommandDeclaration = MkCommandDeclaration
  { cmddecl_loc :: Loc
    -- ^ The source code location of the declaration.
  , cmddecl_doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , cmddecl_name :: FreeVarName
    -- ^ The name of the command.
  , cmddecl_cmd :: Term
    -- ^ The command itself.
  }

deriving instance (Show CommandDeclaration)

---------------------------------------------------------------------------------
-- Structural Xtor Declaration
---------------------------------------------------------------------------------

-- | A toplevel declaration of a constructor or destructor.
-- These declarations are needed for structural data and codata types.
data StructuralXtorDeclaration = MkStructuralXtorDeclaration
  { 
    strxtordecl_loc :: Loc
    -- ^ The source code location of the declaration.
  , strxtordecl_doc :: Maybe DocComment
    -- ^ The documenation string of the declaration.
  , strxtordecl_xdata :: DataCodata
    -- ^ Indicates whether a constructor (Data) or destructor (Codata) is declared.
  , strxtordecl_name :: XtorName
    -- ^ The name of the declared constructor or destructor.
  , strxtordecl_arity :: [(PrdCns, MonoKind)]
    -- ^ The arguments of the constructor/destructor.
    -- Each argument can either be a constructor or destructor.
    -- The MonoKind (CBV or CBN) of each argument has to be specified.
  , strxtordecl_evalOrder :: Maybe EvaluationOrder
    -- Optional evaluation order of the structural type to which the
    -- constructor/destructor belongs.
    -- If no evaluation order is indicated, then it will default to CBV for constructors
    -- and CBN for destructors.
  }

deriving instance (Show StructuralXtorDeclaration)

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data Declaration where 
  PrdCnsDecl     :: PrdCnsDeclaration  -> Declaration
  CmdDecl        :: CommandDeclaration -> Declaration
  DataDecl       :: Loc -> Maybe DocComment -> DataDecl                                                                     -> Declaration
  XtorDecl       :: StructuralXtorDeclaration -> Declaration
  ImportDecl     :: Loc -> Maybe DocComment -> ModuleName                                                                   -> Declaration
  SetDecl        :: Loc -> Maybe DocComment -> Text                                                                         -> Declaration
  TyOpDecl       :: Loc -> Maybe DocComment -> TyOpName -> Precedence -> Associativity -> TypeName                          -> Declaration
  TySynDecl      :: Loc -> Maybe DocComment -> TypeName -> Typ                                                              -> Declaration
  ParseErrorDecl ::                                                                                                            Declaration

instance Show Declaration where
  show _ = "<Show for Declaration not implemented>"

type Program = [Declaration]