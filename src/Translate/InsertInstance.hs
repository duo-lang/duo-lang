module Translate.InsertInstance where

import TypeInference.Constraints (InstanceResult(..))
import Syntax.TST.Terms
import Syntax.TST.Program (InstanceDeclaration(..))
import qualified Data.List.NonEmpty as NE
import Errors
import qualified Data.Map as M
import Pretty.Pretty (ppPrint)
import Pretty.Common


class InsertInstance a where
    insertInstance :: InstanceResult -> a -> Either (NE.NonEmpty Error) a

instance InsertInstance (Term pc) where
    insertInstance inst (Xtor loc ann pc ty ns xtor subst) = Xtor loc ann pc ty ns xtor <$> insertInstance inst subst
    insertInstance inst (XCase loc ann pc ty ns cases) = XCase loc ann pc ty ns <$> mapM (insertInstance inst) cases
    insertInstance inst (MuAbs loc ann pc ty var cmd) = MuAbs loc ann pc ty var <$> insertInstance inst cmd
    insertInstance _inst tm = pure tm

instance InsertInstance CmdCase where
    insertInstance inst (MkCmdCase loc pat cmd) = MkCmdCase loc pat <$> insertInstance inst cmd

instance InsertInstance PrdCnsTerm where
    insertInstance inst (PrdTerm tm) = PrdTerm <$> insertInstance inst tm
    insertInstance inst (CnsTerm tm) = CnsTerm <$> insertInstance inst tm

instance InsertInstance Substitution where
    insertInstance inst (MkSubstitution tms) = MkSubstitution <$> mapM (insertInstance inst) tms

instance InsertInstance Command where
    insertInstance inst (Apply loc ann k prd cns) = Apply loc ann k <$> insertInstance inst prd <*> insertInstance inst cns
    insertInstance inst (Print loc prd cmd) = Print loc <$> insertInstance inst prd <*> insertInstance inst cmd
    insertInstance inst (Read loc cns) = Read loc <$> insertInstance inst cns
    insertInstance inst (Method loc mn cn (InstanceResolved i) ty subst) = Method loc mn cn (InstanceResolved i) ty <$> insertInstance inst subst
    insertInstance (MkInstanceResult m) (Method loc mn cn (InstanceUnresolved uv) ty subst) = case M.lookup (uv, cn) m of
        Nothing -> throwOtherError loc [ "Something went wrong. No instance could be resolved for " <> ppPrint cn <> " " <> ppPrint uv ]
        Just (i, _, _) -> Method loc mn cn (InstanceResolved i) ty <$> insertInstance (MkInstanceResult m) subst
    insertInstance inst (PrimOp loc op subst) = PrimOp loc op <$> insertInstance inst subst
    insertInstance _inst cmd = pure cmd

instance InsertInstance InstanceDeclaration where
    insertInstance inst (MkInstanceDeclaration { instancedecl_loc, instancedecl_doc, instancedecl_name, instancedecl_class, instancedecl_typ, instancedecl_cases }) = do
        insertedCases <- mapM (insertInstance inst) instancedecl_cases
        pure MkInstanceDeclaration
          { instancedecl_loc = instancedecl_loc
          , instancedecl_doc = instancedecl_doc
          , instancedecl_name = instancedecl_name
          , instancedecl_class = instancedecl_class
          , instancedecl_typ = instancedecl_typ
          , instancedecl_cases = insertedCases
          }

instance InsertInstance InstanceCase where
    insertInstance inst (MkInstanceCase { instancecase_loc, instancecase_pat, instancecase_cmd }) = do
        insertedCmd <- insertInstance inst instancecase_cmd
        pure MkInstanceCase 
          { instancecase_loc = instancecase_loc
          , instancecase_pat = instancecase_pat
          , instancecase_cmd = insertedCmd
          }