module Dualize.Program where

import Syntax.CST.Kinds
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCnsRep(..))
import Syntax.RST.Types (PolarityRep(..))
import Syntax.TST.Types qualified as TST
import Syntax.TST.Program qualified as TST
import Dualize.Terms


flipDC :: CST.DataCodata -> CST.DataCodata
flipDC CST.Data = CST.Codata 
flipDC CST.Codata = CST.Data 

dualPolyKind :: PolyKind -> PolyKind 
dualPolyKind pk = pk 

dualDataDecl :: TST.DataDecl -> TST.DataDecl
dualDataDecl TST.NominalDecl { data_loc, data_doc, data_name, data_polarity, data_kind, data_xtors = (sigsPos,sigsNeg) } =
    TST.NominalDecl { data_loc = data_loc
                    , data_doc = data_doc
                    , data_name = dualRnTypeName data_name
                    , data_polarity = flipDC data_polarity
                    , data_kind = dualPolyKind data_kind
                    , data_xtors = (dualXtorSig PosRep <$> sigsPos,dualXtorSig NegRep <$> sigsNeg )
                    }
dualDataDecl TST.RefinementDecl { data_loc
                                , data_doc
                                , data_name
                                , data_polarity
                               , data_refinement_empty = (refinementEmptyPos, refinementEmptyNeg)
                               , data_refinement_full = (refinementFullPos, refinementFullNeg)
                                , data_kind
                                , data_xtors = (sigsPos,sigsNeg)
                                , data_xtors_refined = (sigsPosRefined, sigsNegRefined) } = do
    let refinementEmptyNeg' = refinementEmptyNeg
    let refinementEmptyPos' = refinementEmptyPos
    let refinementFullNeg' = refinementFullNeg
    let refinementFullPos' = refinementFullPos

    TST.RefinementDecl { data_loc = data_loc
                       , data_doc = data_doc
                       , data_name = dualRnTypeName data_name
                       , data_polarity = flipDC data_polarity
                       , data_refinement_empty = ( dualType NegRep refinementEmptyNeg'
                                                 , dualType PosRep refinementEmptyPos')
                       , data_refinement_full = ( dualType NegRep refinementFullNeg'
                                                , dualType PosRep refinementFullPos')
                       , data_kind = dualPolyKind data_kind
                       , data_xtors = (dualXtorSig PosRep <$> sigsPos,dualXtorSig NegRep <$> sigsNeg)
                       , data_xtors_refined = (dualXtorSig PosRep <$> sigsPosRefined,dualXtorSig NegRep <$> sigsNegRefined )
                     }

dualXtorSig ::  PolarityRep pol ->TST.XtorSig pol -> TST.XtorSig pol
dualXtorSig pol (TST.MkXtorSig xtor lctx) = TST.MkXtorSig (dualXtorName xtor) (dualPrdCnsType pol <$> lctx)


dualPrdCnsType :: PolarityRep pol -> TST.PrdCnsType pol -> TST.PrdCnsType pol
dualPrdCnsType PosRep (TST.PrdCnsType PrdRep ty) = TST.PrdCnsType CnsRep (TST.TyFlipPol NegRep ty)
dualPrdCnsType NegRep (TST.PrdCnsType PrdRep ty) = TST.PrdCnsType CnsRep (TST.TyFlipPol PosRep ty)
dualPrdCnsType PosRep (TST.PrdCnsType CnsRep ty) = TST.PrdCnsType PrdRep (TST.TyFlipPol PosRep ty)
dualPrdCnsType NegRep (TST.PrdCnsType CnsRep ty) = TST.PrdCnsType PrdRep (TST.TyFlipPol NegRep ty)

