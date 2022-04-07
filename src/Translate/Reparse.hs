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
  )where


import Control.Monad.State
import Data.Bifunctor
import Data.Text qualified as T
import Data.Maybe (fromJust)

import Syntax.Common
import Syntax.CST.Program qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.CST.Terms qualified as CST
import Syntax.RST.Program qualified as RST
import Syntax.RST.Types qualified as RST
import Syntax.RST.Terms qualified as RST
import Utils

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
openTermCase RST.MkTermCase { tmcase_ext, tmcase_name, tmcase_args, tmcase_term } =
    RST.MkTermCase { tmcase_ext = tmcase_ext
                   , tmcase_name = tmcase_name
                   , tmcase_args = tmcase_args
                   , tmcase_term = RST.termOpening (freeVarNamesToXtorArgs tmcase_args) (openTermComplete tmcase_term)
                   }

openTermCaseI :: RST.TermCaseI pc -> RST.TermCaseI pc
openTermCaseI RST.MkTermCaseI { tmcasei_ext, tmcasei_name, tmcasei_args = (as1, (), as2), tmcasei_term } =
  RST.MkTermCaseI { tmcasei_ext = tmcasei_ext
                  , tmcasei_name = tmcasei_name
                  , tmcasei_args = (as1, (), as2)
                  , tmcasei_term = RST.termOpening (freeVarNamesToXtorArgs (as1 ++ [(Cns, Nothing)] ++ as2)) (openTermComplete tmcasei_term)
                  }

openCmdCase :: RST.CmdCase -> RST.CmdCase
openCmdCase RST.MkCmdCase { cmdcase_ext, cmdcase_name, cmdcase_args, cmdcase_cmd } =
  RST.MkCmdCase { cmdcase_ext = cmdcase_ext
                , cmdcase_name = cmdcase_name
                , cmdcase_args = cmdcase_args
                , cmdcase_cmd = RST.commandOpening (freeVarNamesToXtorArgs cmdcase_args) (openCommandComplete cmdcase_cmd)
                }

openPCTermComplete :: RST.PrdCnsTerm -> RST.PrdCnsTerm
openPCTermComplete (RST.PrdTerm tm) = RST.PrdTerm $ openTermComplete tm
openPCTermComplete (RST.CnsTerm tm) = RST.CnsTerm $ openTermComplete tm

openTermComplete :: RST.Term pc -> RST.Term pc
openTermComplete (RST.BoundVar loc pc idx) =
  RST.BoundVar loc pc idx
openTermComplete (RST.FreeVar loc pc v) =
  RST.FreeVar loc pc v
openTermComplete (RST.Xtor loc pc ns xt args) =
  RST.Xtor loc pc ns xt (openPCTermComplete <$> args)
openTermComplete (RST.XMatch loc pc ns cases) =
  RST.XMatch loc pc ns (openCmdCase <$> cases)
openTermComplete (RST.MuAbs loc PrdRep (Just fv) cmd) =
  RST.MuAbs loc PrdRep (Just fv) (RST.commandOpening [RST.CnsTerm (RST.FreeVar defaultLoc CnsRep fv)] (openCommandComplete cmd))
openTermComplete (RST.MuAbs loc CnsRep (Just fv) cmd) =
  RST.MuAbs loc CnsRep (Just fv) (RST.commandOpening [RST.PrdTerm (RST.FreeVar defaultLoc PrdRep fv)] (openCommandComplete cmd))
openTermComplete (RST.MuAbs _ _ Nothing _) =
  error "Create names first!"
openTermComplete (RST.Dtor loc rep ns xt t (args1,pcrep,args2)) =
  RST.Dtor loc rep ns xt (openTermComplete t) (openPCTermComplete <$> args1,pcrep, openPCTermComplete <$> args2)
openTermComplete (RST.Case loc ns t cases) =
  RST.Case loc ns (openTermComplete t) (openTermCase <$> cases)
openTermComplete (RST.Cocase loc ns cocases) =
  RST.Cocase loc ns (openTermCaseI <$> cocases)
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
createNamesTerm (RST.BoundVar loc pc idx) =
  pure $ RST.BoundVar loc pc idx
createNamesTerm (RST.FreeVar loc pc nm) =
  pure $ RST.FreeVar loc pc nm
createNamesTerm (RST.Xtor loc pc ns xt subst) = do
  subst' <- createNamesSubstitution subst
  pure $ RST.Xtor loc pc ns xt subst'
createNamesTerm (RST.XMatch loc pc ns cases) = do
  cases' <- mapM createNamesCmdCase cases
  pure $ RST.XMatch loc pc ns cases'
createNamesTerm (RST.MuAbs loc pc _ cmd) = do
  cmd' <- createNamesCommand cmd
  var <- fresh (case pc of PrdRep -> Cns; CnsRep -> Prd)
  pure $ RST.MuAbs loc pc var cmd'
createNamesTerm (RST.Dtor loc pc ns xt e (subst1,pcrep,subst2)) = do
  e' <- createNamesTerm e
  subst1' <- createNamesSubstitution subst1
  subst2' <- createNamesSubstitution subst2
  pure $ RST.Dtor loc pc ns xt e' (subst1',pcrep,subst2')
createNamesTerm (RST.Case loc ns e cases) = do
  e' <- createNamesTerm e
  cases' <- sequence (createNamesTermCase <$> cases)
  pure $ RST.Case loc ns e' cases'
createNamesTerm (RST.Cocase loc ns cases) = do
  cases' <- sequence (createNamesTermCaseI <$> cases)
  pure $ RST.Cocase loc ns cases'
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

createNamesCmdCase :: RST.CmdCase -> CreateNameM RST.CmdCase
createNamesCmdCase (RST.MkCmdCase { cmdcase_name, cmdcase_args, cmdcase_cmd }) = do
  cmd' <- createNamesCommand cmdcase_cmd
  args <- sequence $ (\(pc,_) -> (fresh pc >>= \v -> return (pc,v))) <$> cmdcase_args
  return $ RST.MkCmdCase defaultLoc cmdcase_name args cmd'

createNamesTermCase :: RST.TermCase pc -> CreateNameM (RST.TermCase pc)
createNamesTermCase (RST.MkTermCase _ xt args e) = do
  e' <- createNamesTerm e
  args' <- sequence $ (\(pc,_) -> (fresh pc >>= \v -> return (pc,v))) <$> args
  return $ RST.MkTermCase defaultLoc xt args' e'

createNamesTermCaseI :: RST.TermCaseI pc -> CreateNameM (RST.TermCaseI pc)
createNamesTermCaseI (RST.MkTermCaseI _ xt (as1, (), as2) e) = do
  e' <- createNamesTerm e
  let f = (\(pc,_) -> fresh pc >>= \v -> return (pc,v))
  as1' <- sequence $ f <$> as1
  as2' <- sequence $ f <$> as2
  return $ RST.MkTermCaseI defaultLoc xt (as1', (), as2') e'

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
embedTerm RST.BoundVar{} =
  error "Should have been removed by opening"
embedTerm (RST.FreeVar loc _ fv) =
  CST.Var loc fv
embedTerm (RST.Xtor loc _ _ xt subst) =
  CST.Xtor loc xt (embedSubst subst)
embedTerm (RST.XMatch loc PrdRep _ cases) =
  CST.XMatch loc Codata (embedCmdCase <$> cases)
embedTerm (RST.XMatch loc CnsRep _ cases) =
  CST.XMatch loc Data (embedCmdCase <$> cases)
embedTerm (RST.MuAbs loc _ fv cmd) =
  CST.MuAbs loc (fromJust fv) (embedCommand cmd)
embedTerm (RST.Dtor loc _ _ xt tm substi) =
  CST.Dtor loc xt (embedTerm tm) (embedSubstI substi)
embedTerm (RST.Case loc _ tm cases) =
  CST.Case loc (embedTerm tm) (embedTermCase <$> cases)
embedTerm (RST.Cocase loc _ cases) =
  CST.Cocase loc (embedTermCaseI <$> cases)
embedTerm (RST.PrimLitI64 loc i) =
  CST.PrimLitI64 loc i
embedTerm (RST.PrimLitF64 loc d) =
  CST.PrimLitF64 loc d

embedPCTerm :: RST.PrdCnsTerm -> CST.PrdCnsTerm
embedPCTerm (RST.PrdTerm tm) = CST.PrdTerm (embedTerm tm)
embedPCTerm (RST.CnsTerm tm) = CST.CnsTerm (embedTerm tm)

embedSubst :: RST.Substitution -> CST.Substitution
embedSubst = fmap embedPCTerm

embedSubstI :: RST.SubstitutionI pc -> CST.SubstitutionI
embedSubstI (subst1,PrdRep,subst2) = (embedSubst subst1, Prd, embedSubst subst2)
embedSubstI (subst1,CnsRep,subst2) = (embedSubst subst1, Cns, embedSubst subst2)

embedCommand :: RST.Command -> CST.Command
embedCommand (RST.Apply loc prd cns) =
  CST.Apply loc (embedTerm prd) (embedTerm cns)
embedCommand (RST.Print loc tm cmd) =
  CST.Print loc (embedTerm tm) (embedCommand cmd)
embedCommand (RST.Read loc cns) =
  CST.Read loc (embedTerm cns)
embedCommand (RST.Jump loc fv) =
  CST.Jump loc fv
embedCommand (RST.ExitSuccess loc) =
  CST.ExitSuccess loc
embedCommand (RST.ExitFailure loc) =
  CST.ExitFailure loc
embedCommand (RST.PrimOp loc ty op subst) =
  CST.PrimOp loc ty op (embedSubst subst)

embedCmdCase :: RST.CmdCase -> CST.CmdCase
embedCmdCase RST.MkCmdCase { cmdcase_ext, cmdcase_name, cmdcase_args, cmdcase_cmd } =
  CST.MkCmdCase { cmdcase_ext = cmdcase_ext
                , cmdcase_name = cmdcase_name
                , cmdcase_args = second fromJust <$> cmdcase_args
                , cmdcase_cmd = embedCommand cmdcase_cmd
                }

embedTermCase :: RST.TermCase pc -> CST.TermCase
embedTermCase RST.MkTermCase { tmcase_ext, tmcase_name, tmcase_args, tmcase_term } =
  CST.MkTermCase { tmcase_ext = tmcase_ext
                 , tmcase_name = tmcase_name
                 , tmcase_args = second fromJust <$> tmcase_args
                 , tmcase_term = embedTerm tmcase_term}

embedTermCaseI :: RST.TermCaseI pc -> CST.TermCaseI
embedTermCaseI RST.MkTermCaseI { tmcasei_ext, tmcasei_name, tmcasei_args = (as1,rep, as2), tmcasei_term } =
  CST.MkTermCaseI { tmcasei_ext = tmcasei_ext
                  , tmcasei_name = tmcasei_name
                  , tmcasei_args = (second fromJust <$> as1, rep, second fromJust <$> as2)
                  , tmcasei_term = embedTerm tmcasei_term}


embedPrdCnsType :: RST.PrdCnsType pol -> CST.PrdCnsTyp 
embedPrdCnsType (RST.PrdCnsType PrdRep ty) = CST.PrdType (embedType ty)
embedPrdCnsType (RST.PrdCnsType CnsRep ty) = CST.CnsType (embedType ty)

embedXtorSig :: RST.XtorSig pol -> CST.XtorSig
embedXtorSig RST.MkXtorSig { sig_name, sig_args } =
  CST.MkXtorSig { sig_name = sig_name
                , sig_args = embedPrdCnsType <$> sig_args
                }

embedVariantTypes :: [RST.VariantType pol] -> [CST.Typ]
embedVariantTypes = fmap embedVariantType

embedVariantType :: RST.VariantType pol -> CST.Typ
embedVariantType (RST.CovariantType ty) = embedType ty
embedVariantType (RST.ContravariantType ty) = embedType ty

embedType :: RST.Typ pol -> CST.Typ
embedType (RST.TyVar _ _ tv)=
  CST.TyVar defaultLoc tv
embedType (RST.TyData _ tn xtors) =
  CST.TyXData defaultLoc Data tn (embedXtorSig <$> xtors)
embedType (RST.TyCodata _ tn xtors) =
  CST.TyXData defaultLoc Codata tn (embedXtorSig <$> xtors)
embedType (RST.TyNominal _ _ nm args) =
  CST.TyNominal defaultLoc nm (embedVariantTypes args)
embedType (RST.TySet PosRep _ []) =
  CST.TyTop defaultLoc
embedType (RST.TySet PosRep _ [ty1,ty2]) =
  CST.TyBinOp defaultLoc (embedType ty1) UnionOp (embedType ty2)
embedType (RST.TySet PosRep knd (ty1:tys)) =
  CST.TyBinOp defaultLoc (embedType ty1) UnionOp (embedType (RST.TySet PosRep knd tys))
embedType (RST.TySet NegRep _ []) =
  CST.TyBot defaultLoc
embedType (RST.TySet NegRep _ [ty1,ty2]) =
  CST.TyBinOp defaultLoc (embedType ty1) InterOp (embedType ty2)
embedType (RST.TySet NegRep knd (ty1:tys)) =
  CST.TyBinOp defaultLoc (embedType ty1) InterOp (embedType (RST.TySet NegRep knd tys))
embedType (RST.TyRec _ tv ty) =
  CST.TyRec defaultLoc  tv (embedType ty)
embedType (RST.TyPrim _ pt) =
  CST.TyPrim defaultLoc pt

embedTypeScheme :: RST.TypeScheme pol -> CST.TypeScheme
embedTypeScheme RST.TypeScheme { ts_loc, ts_vars, ts_monotype } =
  CST.TypeScheme { ts_loc = ts_loc
                 , ts_vars = ts_vars
                 , ts_monotype = embedType ts_monotype
                 }


embedTyDecl :: RST.DataDecl -> CST.DataDecl
embedTyDecl RST.NominalDecl { data_refined, data_name, data_polarity, data_kind, data_xtors } =
  CST.NominalDecl { data_refined = data_refined
                  , data_name = data_name
                  , data_polarity = data_polarity
                  , data_kind = Just data_kind
                  , data_xtors = embedXtorSig <$> fst data_xtors
                  }

---------------------------------------------------------------------------------
-- CreateNames Monad
---------------------------------------------------------------------------------

reparseTerm :: RST.Term pc -> CST.Term
reparseTerm tm = embedTerm (openTermComplete (evalState (createNamesTerm tm) names))

reparsePCTerm :: RST.PrdCnsTerm -> CST.PrdCnsTerm
reparsePCTerm (RST.PrdTerm tm) = CST.PrdTerm (reparseTerm tm)
reparsePCTerm (RST.CnsTerm tm) = CST.CnsTerm (reparseTerm tm)

reparseSubst :: RST.Substitution -> CST.Substitution
reparseSubst = fmap reparsePCTerm

reparseSubstI :: RST.SubstitutionI pc -> CST.SubstitutionI
reparseSubstI (subst1,PrdRep,subst2) = (reparseSubst subst1,Prd,reparseSubst subst2)
reparseSubstI (subst1,CnsRep,subst2) = (reparseSubst subst1,Cns,reparseSubst subst2)

reparseCommand :: RST.Command -> CST.Command
reparseCommand cmd =
  embedCommand (openCommandComplete (evalState (createNamesCommand cmd) names))

reparseCmdCase :: RST.CmdCase -> CST.CmdCase
reparseCmdCase cmdcase =
  embedCmdCase (evalState (createNamesCmdCase cmdcase) names)

reparseTermCase :: RST.TermCase pc -> CST.TermCase
reparseTermCase termcase =
  embedTermCase (evalState (createNamesTermCase termcase) names)

reparseTermCaseI :: RST.TermCaseI pc -> CST.TermCaseI
reparseTermCaseI termcasei =
  embedTermCaseI (evalState (createNamesTermCaseI termcasei) names)

reparseDecl :: RST.Declaration -> CST.Declaration
reparseDecl (RST.PrdCnsDecl loc doc rep isRec fv ts tm) =
  CST.PrdCnsDecl doc loc (case rep of PrdRep -> Prd; CnsRep -> Cns) isRec fv (embedTypeScheme <$> ts) (reparseTerm tm)
reparseDecl (RST.CmdDecl loc doc fv cmd) =
  CST.CmdDecl doc loc fv (reparseCommand cmd)
reparseDecl (RST.DataDecl loc doc decl) =
  CST.DataDecl doc loc (embedTyDecl decl)
reparseDecl (RST.XtorDecl loc doc dc xt args ret) =
  CST.XtorDecl doc loc dc xt args (Just ret)
reparseDecl (RST.ImportDecl loc doc mn) =
  CST.ImportDecl doc loc mn
reparseDecl (RST.SetDecl loc doc txt) =
  CST.SetDecl doc loc txt
reparseDecl (RST.TyOpDecl loc doc op prec assoc ty) =
  CST.TyOpDecl doc loc op prec assoc ty

reparseProgram :: RST.Program -> CST.Program
reparseProgram = fmap reparseDecl