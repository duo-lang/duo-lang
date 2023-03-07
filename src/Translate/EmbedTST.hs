module Translate.EmbedTST
  ( EmbedTST(..)
  ) where

import Syntax.TST.Program qualified as TST
import Syntax.TST.Terms qualified as TST
import Syntax.TST.Types qualified as TST
import Syntax.RST.Types qualified as RST
import Syntax.RST.Program qualified as RST
import qualified Data.Bifunctor as BF (bimap)
import Syntax.Core.Terms qualified as Core
import Syntax.Core.Program qualified as Core

import Data.Bifunctor (bimap, second)
import Syntax.CST.Kinds (PolyKind(..), MonoKind(..), AnyKind(..))

---------------------------------------------------------------------------------
-- A typeclass for embedding TST.X into Core.X
---------------------------------------------------------------------------------

class EmbedTST a b | a -> b where
  embedTST :: a -> b

---------------------------------------------------------------------------------
-- EmbedTST implementation for terms
---------------------------------------------------------------------------------

instance EmbedTST TST.CmdCase Core.CmdCase where
  embedTST :: TST.CmdCase -> Core.CmdCase
  embedTST cmdcase =
      Core.MkCmdCase { cmdcase_loc = cmdcase.cmdcase_loc
                     , cmdcase_pat = cmdcase.cmdcase_pat
                     , cmdcase_cmd = embedTST  cmdcase.cmdcase_cmd
                     }

instance EmbedTST TST.InstanceCase Core.InstanceCase where
  embedTST :: TST.InstanceCase -> Core.InstanceCase
  embedTST icase =
      Core.MkInstanceCase { instancecase_loc = icase.instancecase_loc
                          , instancecase_pat = icase.instancecase_pat
                          , instancecase_cmd = embedTST  icase.instancecase_cmd
                          }

instance EmbedTST TST.PrdCnsTerm Core.PrdCnsTerm where
  embedTST :: TST.PrdCnsTerm -> Core.PrdCnsTerm
  embedTST (TST.PrdTerm tm) = Core.PrdTerm (embedTST tm)
  embedTST (TST.CnsTerm tm) = Core.CnsTerm (embedTST tm)


instance EmbedTST TST.Substitution Core.Substitution where
  embedTST  :: TST.Substitution -> Core.Substitution
  embedTST  = Core.MkSubstitution . fmap embedTST . (\x -> x.unSubstitution)

instance EmbedTST (TST.Term pc) (Core.Term pc) where
  embedTST :: TST.Term pc -> Core.Term pc
  embedTST (TST.BoundVar loc rep _ty idx) =
      Core.BoundVar loc rep idx
  embedTST (TST.FreeVar loc rep _ty idx) =
      Core.FreeVar loc rep idx
  embedTST (TST.Xtor loc annot rep _ty ns xs subst) =
      Core.Xtor loc annot rep ns xs (embedTST subst)
  embedTST (TST.XCase loc annot rep _ty ns cases) =
      Core.XCase loc annot rep ns (embedTST <$> cases)
  embedTST (TST.MuAbs loc annot rep _ty b cmd) =
      Core.MuAbs loc annot rep b (embedTST cmd)
  embedTST (TST.PrimLitI64 loc i) =
      Core.PrimLitI64 loc i
  embedTST (TST.PrimLitF64 loc d) =
      Core.PrimLitF64 loc d
  embedTST (TST.PrimLitChar loc d) =
      Core.PrimLitChar loc d
  embedTST (TST.PrimLitString loc d) =
      Core.PrimLitString loc d


instance EmbedTST TST.Command Core.Command where
  embedTST :: TST.Command -> Core.Command
  embedTST (TST.Apply loc annot _kind prd cns ) =
      Core.Apply loc annot (embedTST prd) (embedTST cns)
  embedTST (TST.Print loc tm cmd) =
      Core.Print loc (embedTST  tm) (embedTST cmd)
  embedTST (TST.Read loc tm) =
      Core.Read loc (embedTST tm)
  embedTST (TST.Jump loc fv) =
      Core.Jump loc fv
  embedTST (TST.Method loc mn cn _inst ty subst) =
      Core.Method loc mn cn (bimap embedTST embedTST <$> ty) (embedTST subst)
  embedTST (TST.ExitSuccess loc) =
      Core.ExitSuccess loc
  embedTST (TST.ExitFailure loc) =
      Core.ExitFailure loc
  embedTST (TST.PrimOp loc op subst) =
      Core.PrimOp loc op (embedTST subst)

---------------------------------------------------------------------------------
-- EmbedTST implementation for types
---------------------------------------------------------------------------------

instance EmbedTST (TST.PrdCnsType pol) (RST.PrdCnsType pol) where
  embedTST :: TST.PrdCnsType pol -> RST.PrdCnsType pol
  embedTST (TST.PrdCnsType pc tp) = RST.PrdCnsType pc (embedTST  tp)

instance EmbedTST (TST.XtorSig pol) (RST.XtorSig pol) where
  embedTST :: TST.XtorSig pol -> RST.XtorSig pol
  embedTST TST.MkXtorSig {sig_name = name, sig_args = cont} =
    RST.MkXtorSig { sig_name = name, sig_args = map embedTST cont}

instance EmbedTST (TST.VariantType pol) (RST.VariantType pol) where
  embedTST :: TST.VariantType pol -> RST.VariantType pol
  embedTST (TST.CovariantType tp) =
    RST.CovariantType (embedTST tp)
  embedTST (TST.ContravariantType tp) =
    RST.ContravariantType (embedTST tp)

instance EmbedTST (TST.TypeScheme pol) (RST.TypeScheme pol) where
  embedTST :: TST.TypeScheme pol -> RST.TypeScheme pol
  embedTST TST.TypeScheme {ts_loc = loc, ts_vars = tyvars, ts_monotype = mt} =
    RST.TypeScheme {ts_loc = loc, ts_vars = map (Data.Bifunctor.second Just) tyvars,  ts_monotype = embedTST mt}

instance EmbedTST (TST.LinearContext pol) (RST.LinearContext pol) where
  embedTST :: TST.LinearContext pol-> RST.LinearContext pol
  embedTST = map embedTST

getAnnotKind :: AnyKind -> Maybe MonoKind
getAnnotKind (MkPknd (MkPolyKind [] eo)) = Just $ CBox eo
getAnnotKind (MkPknd MkPolyKind{}) = Nothing
getAnnotKind (MkEo eo) = Just $ CBox eo
getAnnotKind (MkPknd (KindVar _)) = Nothing 
getAnnotKind MkI64 = Just I64Rep 
getAnnotKind MkF64 = Just F64Rep
getAnnotKind MkChar = Just CharRep 
getAnnotKind MkString = Just StringRep

instance EmbedTST (TST.Typ pol) (RST.Typ pol) where
  embedTST :: TST.Typ pol -> RST.Typ pol
  embedTST (TST.TySkolemVar loc pol pk tv) =
    RST.TyKindAnnot (CBox pk.returnKind) $ RST.TySkolemVar loc pol tv
  embedTST (TST.TyUniVar loc pol knd tv) = case getAnnotKind knd of
    Nothing -> RST.TyUniVar loc pol tv
    Just mk -> RST.TyKindAnnot mk $ RST.TyUniVar loc pol tv
  embedTST (TST.TyRecVar loc pol (MkPolyKind _ rk) tv) =
    RST.TyKindAnnot (CBox rk) $ RST.TyRecVar loc pol tv
  embedTST (TST.TyRecVar loc pol (KindVar _) tv) =
    RST.TyRecVar loc pol tv
  embedTST (TST.TyData loc pol eo xtors) =
    RST.TyKindAnnot (CBox eo) $ RST.TyData loc pol (map embedTST xtors)
  embedTST (TST.TyCodata loc pol eo xtors) =
    RST.TyKindAnnot (CBox eo) $ RST.TyCodata loc pol (map embedTST xtors)
  embedTST (TST.TyDataRefined loc pol pk@(MkPolyKind [] rk) tn xtors) =
    RST.TyKindAnnot (CBox rk) $ RST.TyDataRefined loc pol pk tn (map embedTST xtors)
  embedTST (TST.TyDataRefined loc pol pk tn xtors) =
    RST.TyDataRefined loc pol pk tn (embedTST <$> xtors)
  embedTST (TST.TyCodataRefined loc pol pk@(MkPolyKind [] rk) tn xtors) = 
    RST.TyKindAnnot (CBox rk) $ RST.TyCodataRefined loc pol pk tn (map embedTST xtors)
  embedTST (TST.TyCodataRefined loc pol pk tn xtors) = 
    RST.TyCodataRefined loc pol pk tn (embedTST <$> xtors)
-- if arguments are applied to TyNominal or TyXDataRefined, don't annotate the Kind, otherwise the parser will break after prettyprint
--  embedTST (TST.TyApp loc pol _ (TST.TyNominal loc' pol' polyknd tn) args) = 
--    RST.TyApp loc pol (RST.TyNominal loc' pol' polyknd tn) (embedTST <$> args)
--  embedTST (TST.TyApp loc pol _ (TST.TyDataRefined loc' pol' pk tn xtors) args) = 
--    RST.TyApp loc pol (RST.TyDataRefined loc' pol' pk tn (embedTST <$> xtors)) (embedTST <$> args)
--  embedTST (TST.TyApp loc pol _ (TST.TyCodataRefined loc' pol' pk tn xtors) args) = 
--    RST.TyApp loc pol (RST.TyCodataRefined loc' pol' pk tn (embedTST <$> xtors)) (embedTST <$> args)
  -- if thre is no application, kind annotation is needed, otherwise x:(Nat:CBV) := x will break after prettyprint
  embedTST (TST.TyNominal loc pol pk@(MkPolyKind [] rk) tn) = do
    RST.TyKindAnnot (CBox rk) $ RST.TyNominal loc pol pk tn  
  embedTST (TST.TyNominal loc pol pk tn) = do
    RST.TyNominal loc pol pk tn  
  embedTST (TST.TyApp loc pol _ ty args) = do
    RST.TyApp loc pol (embedTST ty) (embedTST <$> args)
  embedTST (TST.TySyn loc pol tn tp) = 
    case getAnnotKind (TST.getKind tp) of 
      Nothing -> RST.TySyn loc pol tn (embedTST tp)
      Just mk -> RST.TyKindAnnot mk $ RST.TySyn loc pol tn (embedTST tp)
  embedTST (TST.TyBot loc knd ) = case getAnnotKind knd of
    Nothing -> RST.TyBot loc
    Just mk -> RST.TyKindAnnot mk $ RST.TyBot loc
  embedTST (TST.TyTop loc knd ) = case getAnnotKind knd of
    Nothing -> RST.TyTop loc
    Just mk -> RST.TyKindAnnot mk $ RST.TyTop loc
  embedTST (TST.TyUnion loc knd tp1 tp2) = case getAnnotKind knd of
    Nothing -> RST.TyUnion loc (embedTST tp1) (embedTST tp2)
    Just mk -> RST.TyKindAnnot mk $ RST.TyUnion loc (embedTST tp1) (embedTST tp2)
  embedTST (TST.TyInter loc knd tn1 tn2) = case getAnnotKind knd of 
    Nothing -> RST.TyInter loc (embedTST tn1) (embedTST tn2)
    Just mk -> RST.TyKindAnnot mk $ RST.TyInter loc (embedTST tn1) (embedTST tn2)
  embedTST (TST.TyRec loc pol rv tp) = 
    case getAnnotKind (TST.getKind tp) of 
      Nothing -> RST.TyRec loc pol rv (embedTST tp)
      Just mk -> RST.TyKindAnnot mk $ RST.TyRec loc pol rv (embedTST tp)
  embedTST (TST.TyI64 loc pol) =
    RST.TyI64 loc pol
  embedTST (TST.TyF64 loc pol) =
    RST.TyF64 loc pol
  embedTST (TST.TyChar loc pol) =
    RST.TyChar loc pol
  embedTST (TST.TyString loc pol) =
    RST.TyString loc pol
  embedTST (TST.TyFlipPol pol tp) =
    RST.TyFlipPol pol (embedTST tp)

---------------------------------------------------------------------------------
-- EmbedTST implementation for declarations
---------------------------------------------------------------------------------

instance EmbedTST (TST.PrdCnsDeclaration pc) (Core.PrdCnsDeclaration pc) where
  embedTST  :: TST.PrdCnsDeclaration pc -> Core.PrdCnsDeclaration pc
  embedTST decl =
    case decl.pcdecl_annot of
      TST.Annotated tys ->
        Core.MkPrdCnsDeclaration { pcdecl_loc = decl.pcdecl_loc
                                 , pcdecl_doc = decl.pcdecl_doc
                                 , pcdecl_pc = decl.pcdecl_pc
                                 , pcdecl_isRec = decl.pcdecl_isRec
                                 , pcdecl_name = decl.pcdecl_name
                                 , pcdecl_annot = Just (embedTST tys)
                                 , pcdecl_term = embedTST decl.pcdecl_term
                                 }
      TST.Inferred _ ->
        Core.MkPrdCnsDeclaration { pcdecl_loc = decl.pcdecl_loc
                                 , pcdecl_doc = decl.pcdecl_doc
                                 , pcdecl_pc = decl.pcdecl_pc
                                 , pcdecl_isRec = decl.pcdecl_isRec
                                 , pcdecl_name = decl.pcdecl_name
                                 , pcdecl_annot = Nothing
                                 , pcdecl_term = embedTST decl.pcdecl_term
                                 }

instance EmbedTST TST.CommandDeclaration Core.CommandDeclaration where
  embedTST  :: TST.CommandDeclaration -> Core.CommandDeclaration
  embedTST  decl =
      Core.MkCommandDeclaration { cmddecl_loc = decl.cmddecl_loc
                                , cmddecl_doc = decl.cmddecl_doc
                                , cmddecl_name = decl.cmddecl_name
                                , cmddecl_cmd = embedTST decl.cmddecl_cmd
                                }

instance EmbedTST TST.InstanceDeclaration Core.InstanceDeclaration where
  embedTST  :: TST.InstanceDeclaration -> Core.InstanceDeclaration
  embedTST decl =
      Core.MkInstanceDeclaration { instancedecl_loc = decl.instancedecl_loc
                                 , instancedecl_doc = decl.instancedecl_doc
                                 , instancedecl_name = decl.instancedecl_name
                                 , instancedecl_class = decl.instancedecl_class
                                 , instancedecl_typ = BF.bimap embedTST embedTST decl.instancedecl_typ
                                 , instancedecl_cases = embedTST <$> decl.instancedecl_cases
                                 }

instance EmbedTST TST.DataDecl RST.DataDecl where
  embedTST :: TST.DataDecl -> RST.DataDecl
  embedTST TST.NominalDecl { data_loc = loc
                           , data_doc = doc
                           , data_name = tyn
                           , data_polarity = pol
                           , data_kind = polyknd
                           , data_xtors = xtors } = 
    RST.NominalDecl { data_loc = loc
                    , data_doc = doc
                    , data_name= tyn
                    , data_polarity = pol
                    , data_kind = polyknd
                    , data_xtors = BF.bimap (map embedTST) (map embedTST) xtors
                    }

  embedTST TST.RefinementDecl { data_loc = loc
                              , data_doc = doc
                              , data_name = tyn
                              , data_polarity = pol
                              , data_kind = polyknd
                              , data_xtors = xtors } =
    RST.RefinementDecl { data_loc = loc
                       , data_doc = doc
                       , data_name = tyn
                       , data_polarity = pol
                       , data_kind = polyknd
                       , data_xtors = BF.bimap (map embedTST) (map embedTST) xtors
                       }

instance EmbedTST TST.Declaration Core.Declaration where
  embedTST :: TST.Declaration -> Core.Declaration
  embedTST (TST.PrdCnsDecl pcrep decl) =
      Core.PrdCnsDecl pcrep (embedTST decl)
  embedTST (TST.CmdDecl decl) =
      Core.CmdDecl (embedTST decl)
  embedTST (TST.DataDecl decl) =
      Core.DataDecl (embedTST decl)
  embedTST (TST.XtorDecl decl) =
      Core.XtorDecl decl
  embedTST (TST.ImportDecl decl) =
      Core.ImportDecl decl
  embedTST (TST.SetDecl decl) =
      Core.SetDecl decl
  embedTST (TST.TyOpDecl decl) =
      Core.TyOpDecl decl
  embedTST (TST.TySynDecl decl) =
      Core.TySynDecl decl
  embedTST (TST.ClassDecl decl) =
      Core.ClassDecl decl
  embedTST (TST.InstanceDecl decl) =
      Core.InstanceDecl (embedTST decl)


---------------------------------------------------------------------------------
-- EmbedTST implementation for a module
---------------------------------------------------------------------------------

instance EmbedTST TST.Module Core.Module where
  embedTST :: TST.Module -> Core.Module
  embedTST mod =
      Core.MkModule { mod_name = mod.mod_name
                    , mod_libpath = mod.mod_libpath
                    , mod_decls = embedTST  <$> mod.mod_decls
                    }
