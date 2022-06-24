{-# LANGUAGE UndecidableInstances #-}
module Syntax.TST.Program where

import Syntax.Common
import Syntax.TST.Terms( Command, Term )
import Syntax.RST.Program qualified as RST
import Syntax.CST.Program qualified as CST
import Syntax.Common.TypesPol ( DataDecl, TopAnnot )
import Utils ( Loc )


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
  , pcdecl_annot :: TopAnnot (PrdCnsToPol pc)
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
  ImportDecl     :: CST.ImportDeclaration                -> Declaration
  SetDecl        :: CST.SetDeclaration                   -> Declaration
  TyOpDecl       :: RST.TyOpDeclaration                  -> Declaration
  TySynDecl      :: RST.TySynDeclaration                 -> Declaration
  

instance Show Declaration where
  show (PrdCnsDecl PrdRep decl) = show decl
  show (PrdCnsDecl CnsRep decl) = show decl
  show (CmdDecl decl) = show decl
  show (DataDecl decl) = show decl
  show (XtorDecl decl) = show decl
  show (ImportDecl decl) = show decl
  show (SetDecl decl) = show decl
  show (TyOpDecl decl) = show decl
  show (TySynDecl decl) = show decl
  
type Program = [Declaration]