module Dualize.Program where

import Syntax.Common.Polarity
import Syntax.CST.Kinds
import Syntax.Common.PrdCns
import Syntax.CST.Types qualified as CST
import Syntax.RST.Types qualified as RST
import Syntax.RST.Program qualified as RST
import Dualize.Terms
import Translate.Embed

flipDC :: CST.DataCodata -> CST.DataCodata
flipDC CST.Data = CST.Codata 
flipDC CST.Codata = CST.Data 

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
dualPrdCnsType PosRep (RST.PrdCnsType PrdRep ty) = RST.PrdCnsType CnsRep (embedTSTType (dualType' PrdRep (unEmbedType ty)))
dualPrdCnsType NegRep (RST.PrdCnsType PrdRep ty) = RST.PrdCnsType CnsRep (embedTSTType (dualType' CnsRep (unEmbedType ty)))
dualPrdCnsType PosRep (RST.PrdCnsType CnsRep ty) = RST.PrdCnsType PrdRep (embedTSTType (dualType' CnsRep (unEmbedType ty)))
dualPrdCnsType NegRep (RST.PrdCnsType CnsRep ty) = RST.PrdCnsType PrdRep (embedTSTType (dualType' PrdRep (unEmbedType ty)))
