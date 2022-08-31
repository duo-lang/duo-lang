module Dualize.Program where

import Syntax.CST.Kinds
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCnsRep(..))
import Syntax.RST.Types qualified as RST
import Syntax.RST.Types (PolarityRep(..))
import Syntax.RST.Program qualified as RST
import Dualize.Terms
import TypeInference.GenerateConstraints.Definition (checkKind)
import Translate.Embed
import Syntax.RST.Program (DataDecl(data_refinement_lower))

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
                                , data_refinement_lower
                                , data_refinement_upper
                                , data_kind
                                , data_xtors = (sigsPos,sigsNeg)
                                , data_xtors_refined = (sigsPosRefined, sigsNegRefined) } =
    RST.RefinementDecl { data_loc = data_loc
                       , data_doc = data_doc
                       , data_name = dualRnTypeName data_name
                       , data_polarity = flipDC data_polarity
                       , data_refinement_lower = embedTSTType (dualType NegRep (checkKind data_refinement_upper))
                       , data_refinement_upper = embedTSTType (dualType PosRep (checkKind data_refinement_lower))
                       , data_kind = dualPolyKind data_kind
                       , data_xtors = (dualXtorSig PosRep <$> sigsPos,dualXtorSig NegRep <$> sigsNeg)
                       , data_xtors_refined = (dualXtorSig PosRep <$> sigsPosRefined,dualXtorSig NegRep <$> sigsNegRefined )
                       }

dualXtorSig ::  PolarityRep pol -> RST.XtorSig pol -> RST.XtorSig pol
dualXtorSig pol (RST.MkXtorSig xtor lctx) = RST.MkXtorSig (dualXtorName xtor) (dualPrdCnsType pol <$> lctx)


dualPrdCnsType :: PolarityRep pol -> RST.PrdCnsType pol -> RST.PrdCnsType pol
dualPrdCnsType PosRep (RST.PrdCnsType PrdRep ty) = RST.PrdCnsType CnsRep (embedTSTType (dualType' PrdRep (checkKind ty)))
dualPrdCnsType NegRep (RST.PrdCnsType PrdRep ty) = RST.PrdCnsType CnsRep (embedTSTType (dualType' CnsRep (checkKind ty)))
dualPrdCnsType PosRep (RST.PrdCnsType CnsRep ty) = RST.PrdCnsType PrdRep (embedTSTType (dualType' CnsRep (checkKind ty)))
dualPrdCnsType NegRep (RST.PrdCnsType CnsRep ty) = RST.PrdCnsType PrdRep (embedTSTType (dualType' PrdRep (checkKind ty)))
