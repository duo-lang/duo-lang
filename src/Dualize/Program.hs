module Dualize.Program where

import Syntax.Common
import Syntax.Common.TypesPol
import Syntax.RST.Program qualified as RST
import Dualize.Terms
import Syntax.RST.Program (DataDecl(data_polarity))

flipDC :: DataCodata -> DataCodata
flipDC Data = Codata 
flipDC Codata = Data 

dualPolyKind :: PolyKind -> PolyKind 
dualPolyKind pk = pk 

dualDataDecl :: RST.DataDecl -> RST.DataDecl
dualDataDecl RST.NominalDecl { data_loc, data_doc, data_name, data_polarity, data_kind, data_xtors = (xtorsPos, xtorsNeg)} =
    RST.NominalDecl { data_loc = data_loc
                    , data_doc = data_doc
                    , data_name = dualRnTypeName data_name
                    , data_polarity = flipDC data_polarity
                    , data_kind = dualPolyKind data_kind
                    , data_xtors = (dualXtorSig PosRep <$> xtorsPos,dualXtorSig NegRep <$> xtorsNeg)
                    }
dualDataDecl RST.RefinementDecl {data_loc, data_doc, data_name, data_polarity, data_kind, data_upper, data_lower, data_xtors = (xtorsPos, xtorsNeg), data_xtors_refined = (xtorsRefPos, xtorsRefNeg)} =
    RST.RefinementDecl { data_loc= data_loc
                       , data_doc= data_doc
                       , data_name= dualRnTypeName data_name
                       , data_polarity= flipDC data_polarity
                       , data_kind= dualPolyKind data_kind
                       , data_upper= dualType' PrdRep data_lower
                       , data_lower= dualType' CnsRep data_upper
                       , data_xtors= (dualXtorSig PosRep <$> xtorsPos,dualXtorSig NegRep <$> xtorsNeg)
                       , data_xtors_refined = (dualXtorSig PosRep <$> xtorsRefPos,dualXtorSig NegRep <$> xtorsRefNeg)
                       }
--ndualDataDecl (RST.RefinementDecl loc doc rntn dc pk (sigsPos,sigsNeg)) =
--    RST.RefinementDecl loc doc (dualRnTypeName rntn)  (flipDC dc) (dualPolyKind pk) (dualXtorSig PosRep <$> sigsPos,dualXtorSig NegRep <$> sigsNeg )

dualXtorSig ::  PolarityRep pol -> XtorSig pol -> XtorSig pol 
dualXtorSig pol (MkXtorSig xtor lctx) = MkXtorSig (dualXtorName xtor) (dualPrdCnsType pol <$> lctx)

dualPrdCnsType :: PolarityRep pol -> PrdCnsType pol -> PrdCnsType pol
dualPrdCnsType PosRep (PrdCnsType PrdRep ty) = PrdCnsType CnsRep (dualType' PrdRep ty)
dualPrdCnsType NegRep (PrdCnsType PrdRep ty) = PrdCnsType CnsRep (dualType' CnsRep ty)
dualPrdCnsType PosRep (PrdCnsType CnsRep ty) = PrdCnsType PrdRep (dualType' CnsRep ty)
dualPrdCnsType NegRep (PrdCnsType CnsRep ty) = PrdCnsType PrdRep (dualType' PrdRep ty)
