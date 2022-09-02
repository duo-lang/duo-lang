module Dualize.Program where

import Syntax.CST.Kinds
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCnsRep(..))
import Syntax.RST.Types qualified as RST
import Syntax.RST.Types (PolarityRep(..))
import Syntax.RST.Program qualified as RST
import Dualize.Terms
import Translate.Embed
import TypeInference.GenerateConstraints.Kinds
import Driver.Definition

import Data.Map qualified as M 

flipDC :: CST.DataCodata -> CST.DataCodata
flipDC CST.Data = CST.Codata 
flipDC CST.Codata = CST.Data 

dualPolyKind :: PolyKind -> PolyKind 
dualPolyKind pk = pk 

dualDataDecl :: RST.DataDecl -> RST.DataDecl
dualDataDecl decl = decl
--dualDataDecl RST.NominalDecl { data_loc, data_doc, data_name, data_polarity, data_kind, data_xtors = (sigsPos,sigsNeg) } =
--    RST.NominalDecl { data_loc = data_loc
--                    , data_doc = data_doc
--                    , data_name = dualRnTypeName data_name
--                    , data_polarity = flipDC data_polarity
--                    , data_kind = dualPolyKind data_kind
--                    , data_xtors = (dualXtorSig PosRep <$> sigsPos,dualXtorSig NegRep <$> sigsNeg )
--                    }
--dualDataDecl RST.RefinementDecl { data_loc
--                                , data_doc
--                                , data_name
--                                , data_polarity
 --                               , data_refinement_empty = (refinementEmptyPos, refinementEmptyNeg)
 --                               , data_refinement_full = (refinementFullPos, refinementFullNeg)
---                                , data_kind
--                                , data_xtors = (sigsPos,sigsNeg)
--                                , data_xtors_refined = (sigsPosRefined, sigsNegRefined) } = do
--    let env = M.empty
--    refinementEmptyNeg' <- runKindReaderM (checkKind refinementEmptyNeg) env
--    refinementEmptyPos' <- runKindReaderM (checkKind refinementEmptyPos) env
--    refinementFullNeg' <- runKindReaderM (checkKind refinementFullNeg) env
--    refinementFullPos' <- runKindReaderM (checkKind refinementFullPos) env
--    RST.RefinementDecl { data_loc = data_loc
--                       , data_doc = data_doc
--                       , data_name = dualRnTypeName data_name
--                       , data_polarity = flipDC data_polarity
--                       , data_refinement_empty = ( embedTSTType (dualType NegRep refinementEmptyNeg')
--                                                 , embedTSTType (dualType PosRep refinementEmptyPos'))
--                       , data_refinement_full = ( embedTSTType (dualType NegRep refinementFullNeg')
--                                                , embedTSTType (dualType PosRep refinementFullPos'))
--                       , data_kind = dualPolyKind data_kind
--                       , data_xtors = (dualXtorSig PosRep <$> sigsPos,dualXtorSig NegRep <$> sigsNeg)
--                       , data_xtors_refined = (dualXtorSig PosRep <$> sigsPosRefined,dualXtorSig NegRep <$> sigsNegRefined )
  --                     }

dualXtorSig ::  PolarityRep pol -> RST.XtorSig pol -> RST.XtorSig pol
dualXtorSig pol (RST.MkXtorSig xtor lctx) = RST.MkXtorSig (dualXtorName xtor) (dualPrdCnsType pol <$> lctx)


dualPrdCnsType :: PolarityRep pol -> RST.PrdCnsType pol -> RST.PrdCnsType pol
dualPrdCnsType PosRep (RST.PrdCnsType PrdRep ty) = RST.PrdCnsType CnsRep (RST.TyFlipPol NegRep ty)
dualPrdCnsType NegRep (RST.PrdCnsType PrdRep ty) = RST.PrdCnsType CnsRep (RST.TyFlipPol PosRep ty)
dualPrdCnsType PosRep (RST.PrdCnsType CnsRep ty) = RST.PrdCnsType PrdRep (RST.TyFlipPol PosRep ty)
dualPrdCnsType NegRep (RST.PrdCnsType CnsRep ty) = RST.PrdCnsType PrdRep (RST.TyFlipPol NegRep ty)
