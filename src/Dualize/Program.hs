module Dualize.Program where

import Syntax.Common.Polarity
import Syntax.Common.Kinds
import Syntax.Common.XData
import Syntax.Common.PrdCns
import Syntax.Common.TypesPol
import Syntax.RST.Program qualified as RST
import Dualize.Terms

flipDC :: DataCodata -> DataCodata
flipDC Data = Codata 
flipDC Codata = Data 

dualPolyKind :: PolyKind -> PolyKind 
dualPolyKind pk = pk 

dualDataDecl :: RST.DataDecl -> RST.DataDecl
dualDataDecl (RST.NominalDecl loc doc rntn dc pk (sigsPos,sigsNeg)) =
    RST.NominalDecl loc doc (dualRnTypeName rntn)  (flipDC dc) (dualPolyKind pk) (dualXtorSig PosRep <$> sigsPos,dualXtorSig NegRep <$> sigsNeg )
dualDataDecl (RST.RefinementDecl loc doc rntn dc pk (sigsPos,sigsNeg)) =
    RST.RefinementDecl loc doc (dualRnTypeName rntn)  (flipDC dc) (dualPolyKind pk) (dualXtorSig PosRep <$> sigsPos,dualXtorSig NegRep <$> sigsNeg )

dualXtorSig ::  PolarityRep pol -> XtorSig pol -> XtorSig pol 
dualXtorSig pol (MkXtorSig xtor lctx) = MkXtorSig (dualXtorName xtor) (dualPrdCnsType pol <$> lctx)

dualPrdCnsType :: PolarityRep pol -> PrdCnsType pol -> PrdCnsType pol
dualPrdCnsType PosRep (PrdCnsType PrdRep ty) = PrdCnsType CnsRep (dualType' PrdRep ty)
dualPrdCnsType NegRep (PrdCnsType PrdRep ty) = PrdCnsType CnsRep (dualType' CnsRep ty)
dualPrdCnsType PosRep (PrdCnsType CnsRep ty) = PrdCnsType PrdRep (dualType' CnsRep ty)
dualPrdCnsType NegRep (PrdCnsType CnsRep ty) = PrdCnsType PrdRep (dualType' PrdRep ty)
