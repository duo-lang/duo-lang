module Translate.Reparse
  ( reparseTerm
  , reparsePCTerm
  , reparseCommand
  , reparseDecl
  , reparseProgram
  , reparseSubst
  , reparseSubstI
  , reparseCmdCase
  , reparseTermCase
  , reparseTermCaseI
  -- Types
  , embedVariantType
  , embedType
  , embedXtorSig
  , embedPrdCnsType
  , embedTypeScheme
  , embedLinearContext
  , embedTyDecl
  )where


import Control.Monad.State
import Data.Bifunctor
import Data.Text qualified as T
import Data.Maybe (fromJust)

import Syntax.Common
import Syntax.CST.Program qualified as CST
import Syntax.Common.TypesUnpol qualified as CST
import Syntax.CST.Terms qualified as CST
import Syntax.RST.Program qualified as RST
import Syntax.Common.TypesPol qualified as RST
import Syntax.RST.Terms qualified as RST
import Utils
import Syntax.CST.Terms (FVOrStar(FoSStar))
import GHC.Base (NonEmpty ((:|)))
import Syntax.RST.Terms (CmdCase(cmdcase_pat))

---------------------------------------------------------------------------------
-- These functions  translate a locally nameless term into a named representation.
--
-- Use only for prettyprinting! These functions only "undo" the steps in the parser
-- and do not fulfil any semantic properties w.r.t shadowing etc.!
---------------------------------------------------------------------------------

freeVarNamesToXtorArgs :: [(PrdCns, Maybe FreeVarName)] -> RST.Substitution
freeVarNamesToXtorArgs bs = f <$> bs
  where
    f (Prd, Nothing) = error "Create Names first!"
    f (Prd, Just fv) = RST.PrdTerm $ RST.FreeVar defaultLoc PrdRep fv
    f (Cns, Nothing) = error "Create Names first!"
    f (Cns, Just fv) = RST.CnsTerm $ RST.FreeVar defaultLoc CnsRep fv

openTermCase :: RST.TermCase pc -> RST.TermCase pc
openTermCase RST.MkTermCase { tmcase_loc, tmcase_pat = RST.XtorPat loc xt args , tmcase_term } =
    RST.MkTermCase { tmcase_loc = tmcase_loc
                   , tmcase_pat = RST.XtorPat loc xt args
                   , tmcase_term = RST.termOpening (freeVarNamesToXtorArgs args) (openTermComplete tmcase_term)
                   }

openTermCaseI :: RST.TermCaseI pc -> RST.TermCaseI pc
openTermCaseI RST.MkTermCaseI { tmcasei_loc, tmcasei_pat = RST.XtorPatI loc xt (as1, (), as2), tmcasei_term } =
  RST.MkTermCaseI { tmcasei_loc = tmcasei_loc
                  , tmcasei_pat = RST.XtorPatI loc xt (as1, (), as2)
                  , tmcasei_term = RST.termOpening (freeVarNamesToXtorArgs (as1 ++ [(Cns, Nothing)] ++ as2)) (openTermComplete tmcasei_term)
                  }

openCmdCase :: RST.CmdCase -> RST.CmdCase
openCmdCase RST.MkCmdCase { cmdcase_loc, cmdcase_pat = RST.XtorPat loc xt args, cmdcase_cmd } =
  RST.MkCmdCase { cmdcase_loc = cmdcase_loc
                , cmdcase_pat = RST.XtorPat loc xt args
                , cmdcase_cmd = RST.commandOpening (freeVarNamesToXtorArgs args) (openCommandComplete cmdcase_cmd)
                }

openPCTermComplete :: RST.PrdCnsTerm -> RST.PrdCnsTerm
openPCTermComplete (RST.PrdTerm tm) = RST.PrdTerm $ openTermComplete tm
openPCTermComplete (RST.CnsTerm tm) = RST.CnsTerm $ openTermComplete tm

openTermComplete :: RST.Term pc -> RST.Term pc
-- Core constructs
openTermComplete (RST.BoundVar loc pc idx) =
  RST.BoundVar loc pc idx
openTermComplete (RST.FreeVar loc pc v) =
  RST.FreeVar loc pc v
openTermComplete (RST.Xtor loc pc ns xt args) =
  RST.Xtor loc pc ns xt (openPCTermComplete <$> args)
openTermComplete (RST.XCase loc pc ns cases) =
  RST.XCase loc pc ns (openCmdCase <$> cases)
openTermComplete (RST.MuAbs loc PrdRep (Just fv) cmd) =
  RST.MuAbs loc PrdRep (Just fv) (RST.commandOpening [RST.CnsTerm (RST.FreeVar defaultLoc CnsRep fv)] (openCommandComplete cmd))
openTermComplete (RST.MuAbs loc CnsRep (Just fv) cmd) =
  RST.MuAbs loc CnsRep (Just fv) (RST.commandOpening [RST.PrdTerm (RST.FreeVar defaultLoc PrdRep fv)] (openCommandComplete cmd))
openTermComplete (RST.MuAbs _ _ Nothing _) =
  error "Create names first!"
-- Syntactic sugar
openTermComplete (RST.Semi loc rep ns xt (args1, pcrep, args2) t) =
  RST.Semi loc rep ns xt (openPCTermComplete <$> args1, pcrep, openPCTermComplete <$> args2) (openTermComplete t)
openTermComplete (RST.Dtor loc rep ns xt t (args1,pcrep,args2)) =
  RST.Dtor loc rep ns xt (openTermComplete t) (openPCTermComplete <$> args1,pcrep, openPCTermComplete <$> args2)
openTermComplete (RST.CaseOf loc rep ns t cases) =
  RST.CaseOf loc rep ns (openTermComplete t) (openTermCase <$> cases)
openTermComplete (RST.CocaseOf loc rep ns t cases) =
  RST.CocaseOf loc rep ns (openTermComplete t) (openTermCase <$> cases)
openTermComplete (RST.CaseI loc rep ns cases) =
  RST.CaseI loc rep ns (openTermCaseI <$> cases)
openTermComplete (RST.CocaseI loc rep ns cocases) =
  RST.CocaseI loc rep ns (openTermCaseI <$> cocases)
-- Primitive constructs
openTermComplete (RST.PrimLitI64 loc i) =
  RST.PrimLitI64 loc i
openTermComplete (RST.PrimLitF64 loc d) =
  RST.PrimLitF64 loc d

openCommandComplete :: RST.Command -> RST.Command
openCommandComplete (RST.Apply loc t1 t2) =
  RST.Apply loc (openTermComplete t1) (openTermComplete t2)
openCommandComplete (RST.Print loc t cmd) =
  RST.Print loc (openTermComplete t) (openCommandComplete cmd)
openCommandComplete (RST.Read loc cns) =
  RST.Read loc (openTermComplete cns)
openCommandComplete (RST.Jump loc fv) =
  RST.Jump loc fv
openCommandComplete (RST.ExitSuccess loc) =
  RST.ExitSuccess loc
openCommandComplete (RST.ExitFailure loc) =
  RST.ExitFailure loc
openCommandComplete (RST.PrimOp loc pt op subst) =
  RST.PrimOp loc pt op (openPCTermComplete <$> subst)
openCommandComplete (RST.CaseOfCmd loc ns tm cases) =
  RST.CaseOfCmd loc ns (openTermComplete tm) (openCmdCase <$> cases)
openCommandComplete (RST.CocaseOfCmd loc ns tm cases) =
  RST.CocaseOfCmd loc ns (openTermComplete tm) (openCmdCase <$> cases)
openCommandComplete (RST.CaseOfI loc rep ns tm cases) =
  RST.CaseOfI loc rep ns (openTermComplete tm) (openTermCaseI <$> cases)
openCommandComplete (RST.CocaseOfI loc rep ns tm cases) =
  RST.CocaseOfI loc rep ns (openTermComplete tm) (openTermCaseI <$> cases)

---------------------------------------------------------------------------------
-- CreateNames Monad
---------------------------------------------------------------------------------

type CreateNameM a = State ([FreeVarName],[FreeVarName]) a

names :: ([FreeVarName], [FreeVarName])
names =  ((\y -> MkFreeVarName ("x" <> T.pack (show y))) <$> [(1 :: Int)..]
         ,(\y -> MkFreeVarName ("k" <> T.pack (show y))) <$> [(1 :: Int)..])

fresh :: PrdCns -> CreateNameM (Maybe FreeVarName)
fresh Prd = do
  var <- gets (head . fst)
  modify (first tail)
  pure (Just var)
fresh Cns = do
  var  <- gets (head . snd)
  modify (second tail)
  pure (Just var)

createNamesPCTerm :: RST.PrdCnsTerm -> CreateNameM RST.PrdCnsTerm
createNamesPCTerm (RST.PrdTerm tm) = RST.PrdTerm <$> createNamesTerm tm
createNamesPCTerm (RST.CnsTerm tm) = RST.CnsTerm <$> createNamesTerm tm

createNamesSubstitution :: RST.Substitution  -> CreateNameM RST.Substitution
createNamesSubstitution = mapM createNamesPCTerm

createNamesTerm :: RST.Term pc -> CreateNameM (RST.Term pc)
-- Core constructs
createNamesTerm (RST.BoundVar loc pc idx) =
  pure $ RST.BoundVar loc pc idx
createNamesTerm (RST.FreeVar loc pc nm) =
  pure $ RST.FreeVar loc pc nm
createNamesTerm (RST.Xtor loc pc ns xt subst) = do
  subst' <- createNamesSubstitution subst
  pure $ RST.Xtor loc pc ns xt subst'
createNamesTerm (RST.XCase loc pc ns cases) = do
  cases' <- mapM createNamesCmdCase cases
  pure $ RST.XCase loc pc ns cases'
createNamesTerm (RST.MuAbs loc pc _ cmd) = do
  cmd' <- createNamesCommand cmd
  var <- fresh (case pc of PrdRep -> Cns; CnsRep -> Prd)
  pure $ RST.MuAbs loc pc var cmd'
-- Syntactic sugar
createNamesTerm (RST.Semi loc pc ns xt (subst1,pcrep,subst2) e) = do
  e' <- createNamesTerm e
  subst1' <- createNamesSubstitution subst1
  subst2' <- createNamesSubstitution subst2
  pure $ RST.Semi loc pc ns xt (subst1', pcrep, subst2') e'
createNamesTerm (RST.Dtor loc pc ns xt e (subst1,pcrep,subst2)) = do
  e' <- createNamesTerm e
  subst1' <- createNamesSubstitution subst1
  subst2' <- createNamesSubstitution subst2
  pure $ RST.Dtor loc pc ns xt e' (subst1',pcrep,subst2')
createNamesTerm (RST.CaseOf loc rep ns e cases) = do
  e' <- createNamesTerm e
  cases' <- sequence (createNamesTermCase <$> cases)
  pure $ RST.CaseOf loc rep ns e' cases'
createNamesTerm (RST.CocaseOf loc rep ns e cases) = do
  e' <- createNamesTerm e
  cases' <- sequence (createNamesTermCase <$> cases)
  pure $ RST.CocaseOf loc rep ns e' cases'
createNamesTerm (RST.CaseI loc rep ns cases) = do
  cases' <- sequence (createNamesTermCaseI <$> cases)
  pure $ RST.CaseI loc rep ns cases'
createNamesTerm (RST.CocaseI loc rep ns cases) = do
  cases' <- sequence (createNamesTermCaseI <$> cases)
  pure $ RST.CocaseI loc rep ns cases'
-- Primitive constructs
createNamesTerm (RST.PrimLitI64 loc i) =
  pure (RST.PrimLitI64 loc i)
createNamesTerm (RST.PrimLitF64 loc d) =
  pure (RST.PrimLitF64 loc d)

createNamesCommand :: RST.Command -> CreateNameM RST.Command
createNamesCommand (RST.ExitSuccess loc) =
  pure $ RST.ExitSuccess loc
createNamesCommand (RST.ExitFailure loc) =
  pure $ RST.ExitFailure loc
createNamesCommand (RST.Jump loc fv) =
  pure $ RST.Jump loc fv
createNamesCommand (RST.Apply loc prd cns) = do
  prd' <- createNamesTerm prd
  cns' <- createNamesTerm cns
  pure $ RST.Apply loc prd' cns'
createNamesCommand (RST.Print loc prd cmd) = do
  prd' <- createNamesTerm prd
  cmd' <- createNamesCommand cmd
  pure $ RST.Print loc prd' cmd'
createNamesCommand (RST.Read loc cns) = do
  cns' <- createNamesTerm cns
  pure $ RST.Read loc cns'
createNamesCommand (RST.PrimOp loc pt pop subst) = do
  subst' <- sequence $ createNamesPCTerm <$> subst
  pure $ RST.PrimOp loc pt pop subst'
createNamesCommand (RST.CaseOfCmd loc ns tm cases) = do
  tm' <- createNamesTerm tm
  cases' <- sequence $ createNamesCmdCase <$> cases
  pure $ RST.CaseOfCmd loc ns tm' cases'
createNamesCommand (RST.CocaseOfCmd loc ns tm cases) = do
  tm' <- createNamesTerm tm
  cases' <- sequence $ createNamesCmdCase <$> cases
  pure $ RST.CocaseOfCmd loc ns tm' cases'
createNamesCommand (RST.CaseOfI loc rep ns tm cases) = do
  tm' <- createNamesTerm tm
  cases' <- sequence $ createNamesTermCaseI <$> cases
  pure $ RST.CaseOfI loc rep ns tm' cases'
createNamesCommand (RST.CocaseOfI loc rep ns tm cases) = do
  tm' <- createNamesTerm tm
  cases' <- sequence $ createNamesTermCaseI <$> cases
  pure $ RST.CocaseOfI loc rep ns tm' cases'

createNamesPat :: RST.Pattern -> CreateNameM RST.Pattern
createNamesPat (RST.XtorPat loc xt args) = do
  args' <- sequence $ (\(pc,_) -> (fresh pc >>= \v -> return (pc,v))) <$> args
  pure $ RST.XtorPat loc xt args'

createNamesPatI :: RST.PatternI -> CreateNameM RST.PatternI
createNamesPatI (RST.XtorPatI loc xt (as1, (), as2)) = do
  let f = (\(pc,_) -> fresh pc >>= \v -> return (pc,v))
  as1' <- sequence $ f <$> as1
  as2' <- sequence $ f <$> as2
  pure $ RST.XtorPatI loc xt (as1', (), as2')

createNamesCmdCase :: RST.CmdCase -> CreateNameM RST.CmdCase
createNamesCmdCase RST.MkCmdCase { cmdcase_loc, cmdcase_pat, cmdcase_cmd } = do
  pat' <- createNamesPat cmdcase_pat
  cmd' <- createNamesCommand cmdcase_cmd
  pure $ RST.MkCmdCase cmdcase_loc pat' cmd'

createNamesTermCase :: RST.TermCase pc -> CreateNameM (RST.TermCase pc)
createNamesTermCase RST.MkTermCase { tmcase_loc, tmcase_pat, tmcase_term } = do
  term <- createNamesTerm tmcase_term
  pat <- createNamesPat tmcase_pat
  pure $ RST.MkTermCase tmcase_loc pat term

createNamesTermCaseI :: RST.TermCaseI pc -> CreateNameM (RST.TermCaseI pc)
createNamesTermCaseI RST.MkTermCaseI { tmcasei_loc, tmcasei_pat, tmcasei_term } = do
  term <- createNamesTerm tmcasei_term
  pat <- createNamesPatI tmcasei_pat
  pure $ RST.MkTermCaseI tmcasei_loc pat term

---------------------------------------------------------------------------------
-- CreateNames Monad
---------------------------------------------------------------------------------

isNumSTermRST :: RST.Term pc -> Maybe Int
isNumSTermRST (RST.Xtor _ PrdRep Nominal (MkXtorName "Z") []) = Just 0
isNumSTermRST (RST.Xtor _ PrdRep Nominal (MkXtorName "S") [RST.PrdTerm n]) = case isNumSTermRST n of
  Nothing -> Nothing
  Just n -> Just (n + 1)
isNumSTermRST _ = Nothing

embedTerm :: RST.Term pc -> CST.Term
embedTerm (isNumSTermRST -> Just i) =
  CST.NatLit defaultLoc Nominal i
-- Core constructs
embedTerm RST.BoundVar{} =
  error "Should have been removed by opening"
embedTerm (RST.FreeVar loc _ fv) =
  CST.Var loc fv
embedTerm (RST.Xtor loc _ _ xt subst) =
  CST.Xtor loc xt (CST.ToSTerm <$> (embedSubst subst))
embedTerm (RST.XCase loc PrdRep _ cases) =
  CST.Cocase loc (embedCmdCase <$> cases)
embedTerm (RST.XCase loc CnsRep _ cases) =
  CST.Case loc (embedCmdCase <$> cases)
embedTerm (RST.MuAbs loc _ fv cmd) =
  CST.MuAbs loc (fromJust fv) (embedCommand cmd)
-- Syntactic sugar
embedTerm (RST.Semi loc _ _ xt substi tm) =
  CST.Semi loc xt (embedSubstI substi) (embedTerm tm)
embedTerm (RST.Dtor (Loc s1 s2) _ _ xt tm substi) =
  CST.DtorChain s1  (embedTerm tm) ((xt,embedSubstI substi,s2) :| []  )
embedTerm (RST.CaseOf loc _ _ tm cases) =
  CST.CaseOf loc (embedTerm tm) (embedTermCase <$> cases)
embedTerm (RST.CocaseOf loc _ _ tm cases) =
  CST.CocaseOf loc (embedTerm tm) (embedTermCase <$> cases)
embedTerm (RST.CaseI loc _ _ cases) =
  CST.Case loc (embedTermCaseI <$> cases)
embedTerm (RST.CocaseI loc _ _ cases) =
  CST.Cocase loc (embedTermCaseI <$> cases)
embedTerm (RST.PrimLitI64 loc i) =
  CST.PrimLitI64 loc i
embedTerm (RST.PrimLitF64 loc d) =
  CST.PrimLitF64 loc d


embedPCTerm :: RST.PrdCnsTerm -> CST.Term
embedPCTerm (RST.PrdTerm tm) = embedTerm tm
embedPCTerm (RST.CnsTerm tm) = embedTerm tm

embedSubst :: RST.Substitution -> [CST.Term]
embedSubst = fmap embedPCTerm

embedSubstI :: RST.SubstitutionI pc -> [CST.TermOrStar]
embedSubstI (subst1,PrdRep,subst2) = (CST.ToSTerm <$> embedSubst subst1) ++ [CST.ToSStar] ++  (CST.ToSTerm <$> embedSubst subst2)
embedSubstI (subst1,CnsRep,subst2) = (CST.ToSTerm <$> embedSubst subst1) ++ [CST.ToSStar] ++ (CST.ToSTerm <$> embedSubst subst2)

embedCommand :: RST.Command -> CST.Term
embedCommand (RST.Apply loc prd cns) =
  CST.Apply loc (embedTerm prd) (embedTerm cns)
embedCommand (RST.Print loc tm cmd) =
  CST.PrimCmdTerm $ CST.Print loc (embedTerm tm) (embedCommand cmd)
embedCommand (RST.Read loc cns) =
  CST.PrimCmdTerm $ CST.Read loc (embedTerm cns)
embedCommand (RST.Jump loc fv) =
  CST.Var loc fv
embedCommand (RST.ExitSuccess loc) =
  CST.PrimCmdTerm $ CST.ExitSuccess loc
embedCommand (RST.ExitFailure loc) =
  CST.PrimCmdTerm $ CST.ExitFailure loc
embedCommand (RST.PrimOp loc ty op subst) =
  CST.PrimCmdTerm $ CST.PrimOp loc ty op (embedSubst subst)
embedCommand (RST.CaseOfCmd loc _ns tm cases) = 
  CST.CaseOf loc (embedTerm tm) (embedCmdCase <$> cases)
embedCommand (RST.CocaseOfCmd loc _ns tm cases) =
  CST.CocaseOf loc (embedTerm tm) (embedCmdCase <$> cases)
embedCommand (RST.CaseOfI loc _rep _ns tm cases) =
  CST.CaseOf loc (embedTerm tm) (embedTermCaseI <$> cases)
embedCommand (RST.CocaseOfI loc _rep _ns tm cases) =
  CST.CocaseOf loc (embedTerm tm) (embedTermCaseI <$> cases)


embedPat :: RST.Pattern -> CST.TermPat
embedPat (RST.XtorPat loc xt args) =
  CST.XtorPat loc xt (CST.FoSFV . fromJust . snd <$> args)

embedPatI :: RST.PatternI -> CST.TermPat
embedPatI (RST.XtorPatI loc xt (as1,_,as2)) =
  CST.XtorPat loc xt ((CST.FoSFV . fromJust . snd <$> as1) ++ [FoSStar] ++ (CST.FoSFV . fromJust . snd  <$> as2))

embedCmdCase :: RST.CmdCase -> CST.TermCase
embedCmdCase RST.MkCmdCase { cmdcase_loc, cmdcase_pat, cmdcase_cmd } =
  CST.MkTermCase { tmcase_loc = cmdcase_loc
                 , tmcase_pat = embedPat cmdcase_pat
                 , tmcase_term = embedCommand cmdcase_cmd
                 }

embedTermCase :: RST.TermCase pc -> CST.TermCase
embedTermCase RST.MkTermCase { tmcase_loc, tmcase_pat, tmcase_term } =
  CST.MkTermCase { tmcase_loc = tmcase_loc
                 , tmcase_pat = embedPat tmcase_pat
                 , tmcase_term = embedTerm tmcase_term}

embedTermCaseI :: RST.TermCaseI pc -> CST.TermCase
embedTermCaseI RST.MkTermCaseI { tmcasei_loc, tmcasei_pat, tmcasei_term } =
  CST.MkTermCase { tmcase_loc = tmcasei_loc
                 , tmcase_pat = embedPatI tmcasei_pat
                 , tmcase_term = embedTerm tmcasei_term
                 }


embedPrdCnsType :: RST.PrdCnsType pol -> CST.PrdCnsTyp
embedPrdCnsType (RST.PrdCnsType PrdRep ty) = CST.PrdType (embedType ty)
embedPrdCnsType (RST.PrdCnsType CnsRep ty) = CST.CnsType (embedType ty)

embedLinearContext :: RST.LinearContext pol -> CST.LinearContext
embedLinearContext = fmap embedPrdCnsType

embedXtorSig :: RST.XtorSig pol -> CST.XtorSig
embedXtorSig RST.MkXtorSig { sig_name, sig_args } =
  CST.MkXtorSig { sig_name = sig_name
                , sig_args = embedLinearContext sig_args
                }

embedVariantTypes :: [RST.VariantType pol] -> [CST.Typ]
embedVariantTypes = fmap embedVariantType

embedVariantType :: RST.VariantType pol -> CST.Typ
embedVariantType (RST.CovariantType ty) = embedType ty
embedVariantType (RST.ContravariantType ty) = embedType ty

resugarType :: RST.Typ pol -> Maybe CST.Typ
resugarType (RST.TyNominal loc _ _ MkRnTypeName { rnTnName = MkTypeName "Fun" } [RST.ContravariantType tl, RST.CovariantType tr]) =
  Just (CST.TyBinOp loc (embedType tl) (CustomOp (MkTyOpName "->")) (embedType tr))
resugarType (RST.TyNominal loc _ _ MkRnTypeName { rnTnName = MkTypeName "Par" } [RST.CovariantType t1, RST.CovariantType t2]) =
  Just (CST.TyBinOp loc (embedType t1) (CustomOp (MkTyOpName "⅋")) (embedType t2))
resugarType _ = Nothing

embedType :: RST.Typ pol -> CST.Typ
embedType (resugarType -> Just ty) = ty
embedType (RST.TyVar loc _ _ tv) =
  CST.TyVar loc tv
embedType (RST.TyData loc _ tn xtors) =
  CST.TyXData loc Data (rnTnName <$> tn) (embedXtorSig <$> xtors)
embedType (RST.TyCodata loc _ tn xtors) =
  CST.TyXData loc Codata (rnTnName <$> tn) (embedXtorSig <$> xtors)
embedType (RST.TyNominal loc _ _ nm args) =
  CST.TyNominal loc (rnTnName nm) (embedVariantTypes args)
embedType (RST.TySyn loc _ nm _) =
  CST.TyNominal loc (rnTnName nm) []
embedType (RST.TyTop loc _knd) =
  CST.TyTop loc
embedType (RST.TyBot loc _knd) =
  CST.TyBot loc
embedType (RST.TyUnion loc _knd ty ty') =
  CST.TyBinOp loc (embedType ty) UnionOp (embedType ty')
embedType (RST.TyInter loc _knd ty ty') =
  CST.TyBinOp loc (embedType ty) InterOp (embedType ty')
embedType (RST.TyRec loc _ tv ty) =
  CST.TyRec loc tv (embedType ty)
embedType (RST.TyPrim loc _ pt) =
  CST.TyPrim loc pt

embedTypeScheme :: RST.TypeScheme pol -> CST.TypeScheme
embedTypeScheme RST.TypeScheme { ts_loc, ts_vars, ts_monotype } =
  CST.TypeScheme { ts_loc = ts_loc
                 , ts_vars = ts_vars
                 , ts_monotype = embedType ts_monotype
                 }


embedTyDecl :: RST.DataDecl -> CST.DataDecl
embedTyDecl RST.NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors } =
  CST.NominalDecl { data_refined = data_refined
                  , data_name = rnTnName data_name
                  , data_polarity = data_polarity
                  , data_kind = Just data_kind
                  , data_xtors = embedXtorSig <$> fst data_xtors
                  }

---------------------------------------------------------------------------------
-- CreateNames Monad
---------------------------------------------------------------------------------

reparseTerm :: RST.Term pc -> CST.Term
reparseTerm tm = embedTerm (openTermComplete (evalState (createNamesTerm tm) names))

reparsePCTerm :: RST.PrdCnsTerm -> CST.Term
reparsePCTerm (RST.PrdTerm tm) = reparseTerm tm
reparsePCTerm (RST.CnsTerm tm) = reparseTerm tm

reparseSubst :: RST.Substitution -> CST.Substitution
reparseSubst = fmap reparsePCTerm

reparseSubstI :: RST.SubstitutionI pc -> CST.SubstitutionI
reparseSubstI (subst1,_,subst2) =
  (CST.ToSTerm <$> reparseSubst subst1) ++ [CST.ToSStar] ++ (CST.ToSTerm <$> reparseSubst subst2)

reparseCommand :: RST.Command -> CST.Term
reparseCommand cmd =
  embedCommand (openCommandComplete (evalState (createNamesCommand cmd) names))

reparseCmdCase :: RST.CmdCase -> CST.TermCase
reparseCmdCase cmdcase =
  embedCmdCase (evalState (createNamesCmdCase cmdcase) names)

reparseTermCase :: RST.TermCase pc -> CST.TermCase
reparseTermCase termcase =
  embedTermCase (evalState (createNamesTermCase termcase) names)

reparseTermCaseI :: RST.TermCaseI pc -> CST.TermCase
reparseTermCaseI termcasei =
  embedTermCaseI (evalState (createNamesTermCaseI termcasei) names)

reparseDecl :: RST.Declaration -> CST.Declaration
reparseDecl (RST.PrdCnsDecl loc doc rep isRec fv ts tm) =
  CST.PrdCnsDecl loc doc (case rep of PrdRep -> Prd; CnsRep -> Cns) isRec fv (embedTypeScheme <$> ts) (reparseTerm tm)
reparseDecl (RST.CmdDecl loc doc fv cmd) =
  CST.CmdDecl loc doc fv (reparseCommand cmd)
reparseDecl (RST.DataDecl loc doc decl) =
  CST.DataDecl loc doc (embedTyDecl decl)
reparseDecl (RST.XtorDecl loc doc dc xt args ret) =
  CST.XtorDecl loc doc dc xt args (Just ret)
reparseDecl (RST.ImportDecl loc doc mn) =
  CST.ImportDecl loc doc mn
reparseDecl (RST.SetDecl loc doc txt) =
  CST.SetDecl loc doc txt
reparseDecl (RST.TyOpDecl loc doc op prec assoc ty) =
  CST.TyOpDecl loc doc op prec assoc (rnTnName ty)
reparseDecl (RST.TySynDecl loc doc nm (ty,_)) =
  CST.TySynDecl loc doc nm (embedType ty)

reparseProgram :: RST.Program -> CST.Program
reparseProgram = fmap reparseDecl