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
-- Declarations
---------------------------------------------------------------------------------

data Declaration where 
  PrdCnsDecl     :: PrdCnsDeclaration  -> Declaration
  CmdDecl        :: CommandDeclaration -> Declaration
  DataDecl       :: Loc -> Maybe DocComment -> DataDecl                                                                     -> Declaration
  XtorDecl       :: Loc -> Maybe DocComment -> DataCodata -> XtorName -> [(PrdCns, MonoKind)] -> Maybe EvaluationOrder      -> Declaration
  ImportDecl     :: Loc -> Maybe DocComment -> ModuleName                                                                   -> Declaration
  SetDecl        :: Loc -> Maybe DocComment -> Text                                                                         -> Declaration
  TyOpDecl       :: Loc -> Maybe DocComment -> TyOpName -> Precedence -> Associativity -> TypeName                          -> Declaration
  TySynDecl      :: Loc -> Maybe DocComment -> TypeName -> Typ                                                              -> Declaration
  ParseErrorDecl ::                                                                                                            Declaration

instance Show Declaration where
  show _ = "<Show for Declaration not implemented>"

type Program = [Declaration]