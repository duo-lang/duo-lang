module Dualize.Program where

import Syntax.CST.Kinds
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCnsRep(..))
import Syntax.RST.Types qualified as RST
import Syntax.RST.Types (PolarityRep(..))
import Syntax.RST.Program qualified as RST
import Syntax.TST.Types qualified as TST
import Dualize.Terms
import Translate.Embed


flipDC :: CST.DataCodata -> CST.DataCodata
flipDC CST.Data = CST.Codata 
flipDC CST.Codata = CST.Data 

dualPolyKind :: PolyKind -> PolyKind 
dualPolyKind pk = pk 

dualDataDecl :: RST.DataDecl -> RST.DataDecl
dualDataDecl RST.NominalDecl { data_loc, data_doc, data_name, data_polarity, data_kind, data_xtors = (sigsPos,sigsNeg) } =
    RST.NominalDecl { data_loc = data_loc
                    , data_doc = data_doc
                    , data_name = dualRnTypeName data_name
                    , data_polarity = flipDC data_polarity
                    , data_kind = dualPolyKind data_kind
                    , data_xtors = (dualXtorSig PosRep <$> sigsPos,dualXtorSig NegRep <$> sigsNeg )
                    }
dualDataDecl RST.RefinementDecl { data_loc
                                , data_doc
                                , data_name
                                , data_polarity
                               , data_refinement_empty = (refinementEmptyPos, refinementEmptyNeg)
                               , data_refinement_full = (refinementFullPos, refinementFullNeg)
                                , data_kind
                                , data_xtors = (sigsPos,sigsNeg)
                                , data_xtors_refined = (sigsPosRefined, sigsNegRefined) } = do
    let refinementEmptyNeg' = addDefaultMk refinementEmptyNeg (error "This kind should not be read")
    let refinementEmptyPos' = addDefaultMk refinementEmptyPos (error "This kind should not be read")
    let refinementFullNeg' = addDefaultMk refinementFullNeg (error "This kind should not be read")
    let refinementFullPos' = addDefaultMk refinementFullPos (error "This kind should not be read")

    RST.RefinementDecl { data_loc = data_loc
                       , data_doc = data_doc
                       , data_name = dualRnTypeName data_name
                       , data_polarity = flipDC data_polarity
                       , data_refinement_empty = ( embedTSTType (dualType NegRep refinementEmptyNeg')
                                                 , embedTSTType (dualType PosRep refinementEmptyPos'))
                       , data_refinement_full = ( embedTSTType (dualType NegRep refinementFullNeg')
                                                , embedTSTType (dualType PosRep refinementFullPos'))
                       , data_kind = dualPolyKind data_kind
                       , data_xtors = (dualXtorSig PosRep <$> sigsPos,dualXtorSig NegRep <$> sigsNeg)
                       , data_xtors_refined = (dualXtorSig PosRep <$> sigsPosRefined,dualXtorSig NegRep <$> sigsNegRefined )
                     }

dualXtorSig ::  PolarityRep pol -> RST.XtorSig pol -> RST.XtorSig pol
dualXtorSig pol (RST.MkXtorSig xtor lctx) = RST.MkXtorSig (dualXtorName xtor) (dualPrdCnsType pol <$> lctx)


dualPrdCnsType :: PolarityRep pol -> RST.PrdCnsType pol -> RST.PrdCnsType pol
dualPrdCnsType PosRep (RST.PrdCnsType PrdRep ty) = RST.PrdCnsType CnsRep (RST.TyFlipPol NegRep ty)
dualPrdCnsType NegRep (RST.PrdCnsType PrdRep ty) = RST.PrdCnsType CnsRep (RST.TyFlipPol PosRep ty)
dualPrdCnsType PosRep (RST.PrdCnsType CnsRep ty) = RST.PrdCnsType PrdRep (RST.TyFlipPol PosRep ty)
dualPrdCnsType NegRep (RST.PrdCnsType CnsRep ty) = RST.PrdCnsType PrdRep (RST.TyFlipPol NegRep ty)

addDefaultMk :: RST.Typ pol -> MonoKind -> TST.Typ pol
addDefaultMk (RST.TySkolemVar loc pol tv) mk           = TST.TySkolemVar loc pol mk tv
addDefaultMk (RST.TyUniVar loc pol tv) mk              = TST.TyUniVar loc pol mk tv
addDefaultMk (RST.TyRecVar loc pol tv) mk              = TST.TyRecVar loc pol mk tv
addDefaultMk (RST.TyData loc pol xtors) mk             = TST.TyData loc pol mk (map (`addDefaultMkXtorSig` mk ) xtors)
addDefaultMk (RST.TyCodata loc pol xtors) mk           = TST.TyCodata loc pol mk (map (`addDefaultMkXtorSig` mk ) xtors)
addDefaultMk (RST.TyDataRefined loc pol tn xtors) mk   = TST.TyDataRefined loc pol mk tn (map (`addDefaultMkXtorSig` mk ) xtors)
addDefaultMk (RST.TyCodataRefined loc pol tn xtors) mk = TST.TyCodataRefined loc pol mk tn (map (`addDefaultMkXtorSig` mk ) xtors)
addDefaultMk (RST.TyNominal loc pol tn varty) mk       = TST.TyNominal loc pol mk tn (map (`addDefaultMkVarTy` mk) varty)
addDefaultMk (RST.TySyn loc pol tn ty) mk              = TST.TySyn loc pol tn (addDefaultMk ty mk) 
addDefaultMk (RST.TyBot loc) mk                        = TST.TyBot loc mk
addDefaultMk (RST.TyTop loc) mk                        = TST.TyTop loc mk
addDefaultMk (RST.TyUnion loc ty1 ty2) mk              = TST.TyUnion loc mk (addDefaultMk ty1 mk) (addDefaultMk ty2 mk)
addDefaultMk (RST.TyInter loc ty1 ty2) mk              = TST.TyInter loc mk (addDefaultMk ty1 mk) (addDefaultMk ty2 mk)
addDefaultMk (RST.TyRec loc pol rv ty) mk              = TST.TyRec loc pol rv (addDefaultMk ty mk)
addDefaultMk (RST.TyI64 loc pol) _                     = TST.TyI64 loc pol
addDefaultMk (RST.TyF64 loc pol) _                     = TST.TyF64 loc pol
addDefaultMk (RST.TyChar loc pol) _                    = TST.TyChar loc pol
addDefaultMk (RST.TyString loc pol) _                  = TST.TyString loc pol
addDefaultMk (RST.TyFlipPol pol ty) mk                 = TST.TyFlipPol pol (addDefaultMk ty mk)

addDefaultMkXtorSig :: RST.XtorSig pol -> MonoKind -> TST.XtorSig pol
addDefaultMkXtorSig RST.MkXtorSig{sig_name = nm, sig_args = args} mk = TST.MkXtorSig{sig_name = nm, sig_args = map (`addDefaultMkPrdCnsType` mk) args}

addDefaultMkPrdCnsType :: RST.PrdCnsType pol -> MonoKind -> TST.PrdCnsType pol
addDefaultMkPrdCnsType (RST.PrdCnsType pc ty) mk = TST.PrdCnsType pc (addDefaultMk ty mk)

addDefaultMkVarTy :: RST.VariantType pol -> MonoKind -> TST.VariantType pol
addDefaultMkVarTy (RST.CovariantType ty) mk = TST.CovariantType (addDefaultMk ty mk)
addDefaultMkVarTy (RST.ContravariantType ty) mk = TST.ContravariantType (addDefaultMk ty mk)

