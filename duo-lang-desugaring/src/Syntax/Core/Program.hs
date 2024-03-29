module Syntax.Core.Program where

import Syntax.Core.Terms( Command, Term, InstanceCase )
import Syntax.RST.Types qualified as RST
import Syntax.RST.Types (Polarity(..))
import Syntax.RST.Program qualified as RST
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Loc ( Loc )
import Syntax.CST.Names ( ClassName, DocComment, FreeVarName, ModuleName )

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
  , pcdecl_isRec :: CST.IsRec
    -- ^ Whether the declaration can refer to itself recursively.
  , pcdecl_name :: FreeVarName
    -- ^ The name of the producer / consumer.
  , pcdecl_annot :: Maybe (RST.TypeScheme (RST.PrdCnsToPol pc))
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

------------------------------------------------------------------------------
-- Instance Declaration
------------------------------------------------------------------------------

data InstanceDeclaration = MkInstanceDeclaration
  { instancedecl_loc :: Loc
    -- ^ The source code location of the declaration.
  , instancedecl_doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , instancedecl_name :: FreeVarName
    -- ^ The name of the instance declaration.
  , instancedecl_class :: ClassName
    -- ^ The name of the type class the instance is for.
  , instancedecl_typ :: (RST.Typ Pos, RST.Typ Neg)
    -- ^ The type the instance is being defined for.
  , instancedecl_cases :: [InstanceCase]
    -- ^ The method definitions for the class.
  }

deriving instance Show InstanceDeclaration

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data Declaration where
  PrdCnsDecl     :: PrdCnsRep pc -> PrdCnsDeclaration pc -> Declaration
  CmdDecl        :: CommandDeclaration                   -> Declaration
  DataDecl       :: RST.DataDecl                         -> Declaration
  XtorDecl       :: RST.StructuralXtorDeclaration        -> Declaration
  ImportDecl     :: CST.ImportDeclaration                -> Declaration
  SetDecl        :: CST.SetDeclaration                   -> Declaration
  TyOpDecl       :: RST.TyOpDeclaration                  -> Declaration
  TySynDecl      :: RST.TySynDeclaration                 -> Declaration
  ClassDecl      :: RST.ClassDeclaration                 -> Declaration
  InstanceDecl   :: InstanceDeclaration                  -> Declaration
  

instance Show Declaration where
  show (PrdCnsDecl PrdRep decl) = show decl
  show (PrdCnsDecl CnsRep decl) = show decl
  show (CmdDecl           decl) = show decl
  show (DataDecl          decl) = show decl
  show (XtorDecl          decl) = show decl
  show (ImportDecl        decl) = show decl
  show (SetDecl           decl) = show decl
  show (TyOpDecl          decl) = show decl
  show (TySynDecl         decl) = show decl
  show (ClassDecl         decl) = show decl
  show (InstanceDecl      decl) = show decl

---------------------------------------------------------------------------------
-- Module
---------------------------------------------------------------------------------

-- | A module which corresponds to a single '*.duo' file.
data Module = MkModule
  { mod_name :: ModuleName
    -- ^ The name of the module.
  , mod_libpath :: FilePath
    -- ^ The absolute filepath of the library of the module.
  , mod_decls :: [Declaration]
    -- ^ The declarations contained in the module.
  }

deriving instance Show Module
