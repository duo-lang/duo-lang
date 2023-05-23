{-# LANGUAGE UndecidableInstances #-}
module Syntax.TST.Program where

import Syntax.TST.Terms( Command, Term, InstanceCase )
import Syntax.RST.Program qualified as RST
import Syntax.CST.Program qualified as CST
import Syntax.TST.Types ( TopAnnot, Typ, XtorSig)
import Syntax.RST.Types (Polarity(..))
import Syntax.RST.Names (RnTypeName)
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..), DataCodata(..), PolyKind(..))
import Syntax.CST.Names ( ClassName, DocComment, FreeVarName, ModuleName )
import Loc ( Loc )


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
  , pcdecl_annot :: TopAnnot (RST.PrdCnsToPol pc)
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
  , instancedecl_typ :: (Typ Pos, Typ Neg)
    -- ^ The type the instance is being defined for.
  , instancedecl_cases :: [InstanceCase]
    -- ^ The method definitions for the class.
  }

deriving instance Show InstanceDeclaration

------------------------------------------------------------------------------
-- Data Type declarations
------------------------------------------------------------------------------

data DataDecl =
    NominalDecl
  { data_loc :: Loc
    -- ^ The source code location of the declaration.
  , data_doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , data_name :: RnTypeName
    -- ^ The name of the type. E.g. "List".
  , data_polarity :: DataCodata
    -- ^ Whether a data or codata type is declared.
  , data_kind :: PolyKind
    -- ^ The kind of the type constructor.
  , data_xtors :: ([XtorSig Pos], [XtorSig Neg])
    -- The constructors/destructors of the declaration.
  }
  | RefinementDecl
  { data_loc :: Loc
    -- ^ The source code location of the declaration.
  , data_doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , data_name :: RnTypeName
    -- ^ The name of the type. E.g. "List".
  , data_polarity :: DataCodata
    -- ^ Whether a data or codata type is declared.
  , data_refinement_empty :: (Typ Pos, Typ Neg)
    -- ^ The lower bound of the refinement type. E.g. `< Nat | >`
  , data_refinement_full :: (Typ Pos, Typ Neg)
    -- ^ The upper bound of the refinement type. E.g. `mu alpha. < Nat | Z, S(alpha) >`
  , data_kind :: PolyKind
    -- ^ The kind of the type constructor.
  , data_xtors :: ([XtorSig Pos], [XtorSig Neg])
    -- ^ The constructors/destructors of the declaration,
    -- as written by the user.
  , data_xtors_refined :: ([XtorSig Pos], [XtorSig Neg])
    -- ^ The constructors/destructors of the declaration,
    -- with recursive occurrences replaced by the refinement type.
  }
deriving instance Show DataDecl
---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data Declaration where
  PrdCnsDecl     :: PrdCnsRep pc -> PrdCnsDeclaration pc -> Declaration
  CmdDecl        :: CommandDeclaration                   -> Declaration
  DataDecl       :: DataDecl                             -> Declaration
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
--  deriving instance Eq Module
instance Eq Module where
  m1 == m2 = m1.mod_name == m2.mod_name && m1.mod_libpath == m2.mod_libpath
