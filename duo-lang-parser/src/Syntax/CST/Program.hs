module Syntax.CST.Program where

import Data.Text (Text)

import Syntax.CST.Terms ( Term, TermCase )
import Syntax.CST.Types
    ( TypeScheme, XtorSig, Typ, DataCodata, PrdCns, EvaluationOrder, MonoKind, PolyKind, )
import Syntax.CST.Names
    ( Associativity,
      ClassName,
      DocComment,
      FreeVarName,
      ModuleName (..),
      Precedence,
      TyOpName,
      TypeName,
      XtorName )
import Loc ( HasLoc(..), Loc )

---------------------------------------------------------------------------------
-- Producer / Consumer Declaration
---------------------------------------------------------------------------------

data IsRec where
  Recursive :: IsRec
  NonRecursive :: IsRec
  deriving (Show, Eq, Ord)

-- | A toplevel producer or consumer declaration.
data PrdCnsDeclaration = MkPrdCnsDeclaration
  { loc :: Loc
    -- ^ The source code location of the declaration.
  , doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , prd_cns :: PrdCns
    -- ^ Whether a producer or consumer is declared.
  , isRecursive :: IsRec
    -- ^ Whether the declaration can refer to itself recursively.
  , name :: FreeVarName
    -- ^ The name of the producer / consumer.
  , annot :: Maybe TypeScheme
    -- ^ The type signature.
  , term :: Term
    -- ^ The term itself.
}

deriving instance Show PrdCnsDeclaration
deriving instance Eq PrdCnsDeclaration

instance HasLoc PrdCnsDeclaration where
  getLoc decl = decl.loc

---------------------------------------------------------------------------------
-- Command Declaration
---------------------------------------------------------------------------------

-- | A toplevel command declaration.
data CommandDeclaration = MkCommandDeclaration
  { loc :: Loc
    -- ^ The source code location of the declaration.
  , doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , name :: FreeVarName
    -- ^ The name of the command.
  , cmd :: Term
    -- ^ The command itself.
  }

deriving instance Show CommandDeclaration
deriving instance Eq CommandDeclaration

instance HasLoc CommandDeclaration where
  getLoc decl = decl.loc

---------------------------------------------------------------------------------
-- Structural Xtor Declaration
---------------------------------------------------------------------------------

-- | A toplevel declaration of a constructor or destructor.
-- These declarations are needed for structural data and codata types.
data StructuralXtorDeclaration = MkStructuralXtorDeclaration
  {
    loc :: Loc
    -- ^ The source code location of the declaration.
  , doc :: Maybe DocComment
    -- ^ The documenation string of the declaration.
  , data_codata :: DataCodata
    -- ^ Indicates whether a constructor (Data) or destructor (Codata) is declared.
  , name :: XtorName
    -- ^ The name of the declared constructor or destructor.
  , arity :: [(PrdCns, MonoKind)]
    -- ^ The arguments of the constructor/destructor.
    -- Each argument can either be a constructor or destructor.
    -- The MonoKind (CBV or CBN) of each argument has to be specified.
  , evalOrder :: Maybe EvaluationOrder
    -- Optional evaluation order of the structural type to which the
    -- constructor/destructor belongs.
    -- If no evaluation order is indicated, then it will default to CBV for constructors
    -- and CBN for destructors.
  }

deriving instance Show StructuralXtorDeclaration
deriving instance Eq StructuralXtorDeclaration

instance HasLoc StructuralXtorDeclaration where
  getLoc decl = decl.loc

---------------------------------------------------------------------------------
-- Import Declaration
---------------------------------------------------------------------------------

-- | A toplevel import statment.
data ImportDeclaration = MkImportDeclaration
  { loc :: Loc
    -- ^ The source code location of the import.
  , doc :: Maybe DocComment
    -- ^ The documentation string of the import.
  , mod :: ModuleName
    -- ^ The imported module.
  }

deriving instance Show ImportDeclaration
deriving instance Eq ImportDeclaration

instance HasLoc ImportDeclaration where
  getLoc decl = decl.loc

---------------------------------------------------------------------------------
-- Set Declaration
---------------------------------------------------------------------------------

-- | A toplevel configuration option.
data SetDeclaration = MkSetDeclaration
  { loc :: Loc
    -- ^ The source code location of the option.
  , doc :: Maybe DocComment
    -- ^ The documentation string of the option.
  , option :: Text
    -- ^ The option itself.
  }

deriving instance Show SetDeclaration
deriving instance Eq SetDeclaration

instance HasLoc SetDeclaration where
  getLoc decl = decl.loc

---------------------------------------------------------------------------------
-- Type Operator Declaration
---------------------------------------------------------------------------------

-- | A toplevel declaration of a type operator.
data TyOpDeclaration = MkTyOpDeclaration
  { loc :: Loc
    -- ^ The source code location of the declaration.
  , doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , symbol :: TyOpName
    -- ^ The symbol used for the type operator.
  , precedence :: Precedence
    -- ^ The precedence level of the type operator.
  , associativity :: Associativity
    -- ^ The associativity of the type operator.
  , res :: TypeName
    -- ^ The typename that the operator should stand for.
  }

deriving instance Show TyOpDeclaration
deriving instance Eq TyOpDeclaration

instance HasLoc TyOpDeclaration where
  getLoc decl = decl.loc

---------------------------------------------------------------------------------
-- Type Synonym Declaration
---------------------------------------------------------------------------------

-- | A toplevel declaration of a type synonym.
data TySynDeclaration = MkTySynDeclaration
  { loc :: Loc
    -- ^ The source code location of the declaration.
  , doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , name :: TypeName
    -- ^ The name of the type synonym that is being introduced.
  , res :: Typ
    -- ^ What the type synonym should be replaced with.
  }

deriving instance Show TySynDeclaration
deriving instance Eq TySynDeclaration

instance HasLoc TySynDeclaration where
  getLoc decl = decl.loc

------------------------------------------------------------------------------
-- Instance Declaration
------------------------------------------------------------------------------

data InstanceDeclaration = MkInstanceDeclaration
  { loc :: Loc
    -- ^ The source code location of the declaration.
  , doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , instance_name :: FreeVarName
    -- ^ The name of the instance declaration.
  , class_name :: ClassName
    -- ^ The name of the type class the instance is for.
  , typ :: Typ
    -- ^ The type the instance is being defined for.
  , cases :: [TermCase]
    -- ^ The method definitions for the class.
  }

deriving instance Show InstanceDeclaration
deriving instance Eq InstanceDeclaration

instance HasLoc InstanceDeclaration where
  getLoc decl = decl.loc

------------------------------------------------------------------------------
-- Class Declaration
------------------------------------------------------------------------------

data ClassDeclaration = MkClassDeclaration
  { loc :: Loc
    -- ^ The source code location of the declaration.
  , doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , name :: ClassName
    -- ^ The name of the type class that is being introduced.
  , kinds :: PolyKind
    -- ^ The kind of the type class variables.
  , methods :: [XtorSig]
    -- ^ The type class methods and their types.
  }

deriving instance Show ClassDeclaration
deriving instance Eq ClassDeclaration

instance HasLoc ClassDeclaration where
  getLoc decl = decl.loc

------------------------------------------------------------------------------
-- Data Type declarations
------------------------------------------------------------------------------

data IsRefined = Refined | NotRefined
  deriving (Show, Ord, Eq)

-- | A toplevel declaration of a data or codata type.
data DataDecl = MkDataDecl
  { loc :: Loc
    -- ^ The source code location of the declaration.
  , doc :: Maybe DocComment
    -- ^ The documentation string of the declaration.
  , isRefined :: IsRefined
    -- ^ Whether an ordinary or a refinement type is declared.
  , name :: TypeName
    -- ^ The name of the type. E.g. "List".
  , data_codata :: DataCodata
    -- ^ Whether a data or codata type is declared.
  , kind :: Maybe PolyKind
    -- ^ The kind of the type constructor.
  , xtors :: [XtorSig]
    -- The constructors/destructors of the declaration.
  }

deriving instance Show DataDecl
deriving instance Eq DataDecl

instance HasLoc DataDecl where
  getLoc decl = decl.loc

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data Declaration where
  PrdCnsDecl     :: PrdCnsDeclaration         -> Declaration
  CmdDecl        :: CommandDeclaration        -> Declaration
  DataDecl       :: DataDecl                  -> Declaration
  XtorDecl       :: StructuralXtorDeclaration -> Declaration
  ImportDecl     :: ImportDeclaration         -> Declaration
  SetDecl        :: SetDeclaration            -> Declaration
  TyOpDecl       :: TyOpDeclaration           -> Declaration
  TySynDecl      :: TySynDeclaration          -> Declaration
  ClassDecl      :: ClassDeclaration          -> Declaration
  InstanceDecl   :: InstanceDeclaration       -> Declaration
  ParseErrorDecl ::                              Declaration

instance Show Declaration where
  show _ = "<Show for Declaration not implemented>"
deriving instance Eq Declaration

---------------------------------------------------------------------------------
-- Module
---------------------------------------------------------------------------------

-- | A module which corresponds to a single '*.duo' file.
data Module = MkModule
  { name :: ModuleName
    -- ^ The name of the module.
  , libpath :: FilePath
    -- ^ The absolute filepath of the library of the module.
  , decls :: [Declaration]
    -- ^ The declarations contained in the module.
  }

deriving instance Show Module
deriving instance Eq Module
