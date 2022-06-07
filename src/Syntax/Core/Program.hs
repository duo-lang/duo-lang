module Syntax.Core.Program where

import Data.Text (Text)

import Syntax.Common
import Syntax.Core.Terms( Command, Term )
import Syntax.Common.TypesPol ( DataDecl, Typ, TypeScheme )
import Utils ( Loc )
import qualified Syntax.RST.Program as RST

---------------------------------------------------------------------------------
-- Producer / Consumer Declaration
---------------------------------------------------------------------------------

-- | A toplevel producer or consumer declaration.
data PrdCnsDeclaration pc = MkPrdCnsDeclaration
  { pcdecl_loc :: Loc
    -- ^ The source code location of the declaration.
  , pcdecl_doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , pcdecl_pc :: PrdCnsRep pc
    -- ^ Whether a producer or consumer is declared.
  , pcdecl_isRec :: IsRec
    -- ^ Whether the declaration can refer to itself recursively.
  , pcdecl_name :: FreeVarName
    -- ^ The name of the producer / consumer.
  , pcdecl_annot :: Maybe (TypeScheme (PrdCnsToPol pc))
    -- ^ The type signature.
  , pcdecl_term :: Term pc
    -- ^ The term itself.
}

deriving instance (Show (PrdCnsDeclaration Prd))
deriving instance (Show (PrdCnsDeclaration Cns))

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
  , cmddecl_cmd :: Command
    -- ^ The command itself.
  }

deriving instance (Show CommandDeclaration)

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data Declaration where
  PrdCnsDecl     :: PrdCnsRep pc -> PrdCnsDeclaration pc -> Declaration
  CmdDecl        :: CommandDeclaration                   -> Declaration
  DataDecl       :: DataDecl                             -> Declaration
  XtorDecl       :: RST.StructuralXtorDeclaration        -> Declaration
  ImportDecl     :: Loc -> Maybe DocComment -> ModuleName                                                                   -> Declaration
  SetDecl        :: Loc -> Maybe DocComment -> Text                                                                         -> Declaration
  TyOpDecl       :: Loc -> Maybe DocComment -> TyOpName -> Precedence -> Associativity -> RnTypeName                        -> Declaration
  TySynDecl      :: Loc -> Maybe DocComment -> TypeName -> (Typ Pos, Typ Neg)                                               -> Declaration
  

instance Show Declaration where
  show (PrdCnsDecl PrdRep decl) = show decl
  show (PrdCnsDecl CnsRep decl) = show decl
  show (CmdDecl decl) = show decl
  show (DataDecl decl) = show decl
  show (XtorDecl decl) = show decl
  show (ImportDecl loc doc mn) = "ImportDecl: " ++ show loc ++ show doc ++ show mn
  show (SetDecl loc doc txt) = "SetDecl: " ++ show loc ++ show doc ++ show txt
  show (TyOpDecl loc doc op prec assoc ty) = "TyOpDecl: " ++ show loc ++ show doc ++ show op ++ show prec ++ show assoc ++ show ty
  show (TySynDecl loc doc nm ty) = "TySynDecl: " ++ show loc ++ show doc ++ show nm ++ show ty
  
type Program = [Declaration]