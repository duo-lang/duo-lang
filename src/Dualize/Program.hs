module Dualize.Program where

import Syntax.Common.Polarity
import Syntax.Common.Kinds
import Syntax.Common.XData
import Syntax.Common.PrdCns
import Syntax.RST.Types qualified as RST
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

dualXtorSig ::  PolarityRep pol -> RST.XtorSig pol -> RST.XtorSig pol 
dualXtorSig pol (RST.MkXtorSig xtor lctx) = RST.MkXtorSig (dualXtorName xtor) (dualPrdCnsType pol <$> lctx)

dualPrdCnsType :: PolarityRep pol -> RST.PrdCnsType pol -> RST.PrdCnsType pol
dualPrdCnsType PosRep (RST.PrdCnsType PrdRep ty) = RST.PrdCnsType CnsRep (dualType' PrdRep ty)
dualPrdCnsType NegRep (RST.PrdCnsType PrdRep ty) = RST.PrdCnsType CnsRep (dualType' CnsRep ty)
dualPrdCnsType PosRep (RST.PrdCnsType CnsRep ty) = RST.PrdCnsType PrdRep (dualType' CnsRep ty)
dualPrdCnsType NegRep (RST.PrdCnsType CnsRep ty) = RST.PrdCnsType PrdRep (dualType' PrdRep ty)
