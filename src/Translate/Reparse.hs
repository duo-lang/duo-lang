module Translate.Reparse
  ( reparseTerm
  , reparsePrdCnsTerm
  , reparseCommand
  , reparseDecl
  , reparseProgram
  ) where

import Control.Monad.State
import Data.Bifunctor
import Data.Text qualified as T

import Syntax.Common
import Syntax.RST.Program qualified as RST
import Syntax.RST.Terms qualified as RST
import Syntax.CST.Program qualified as CST
import Syntax.CST.Terms qualified as CST
import Utils

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

reparsePrdCnsTerm :: RST.PrdCnsTerm -> RST.PrdCnsTerm
reparsePrdCnsTerm = undefined

reparseTerm :: RST.Term pc -> RST.Term pc
reparseTerm tm = evalState (createNamesTerm tm) names

reparseCommand :: RST.Command -> RST.Command
reparseCommand cmd = evalState (createNamesCommand cmd) names

reparseDecl :: RST.Declaration -> RST.Declaration
reparseDecl (RST.PrdCnsDecl loc doc rep isRec fv ts tm) =
  RST.PrdCnsDecl loc doc rep isRec fv ts (reparseTerm tm)
reparseDecl (RST.CmdDecl loc doc fv cmd) =
  RST.CmdDecl loc doc fv (reparseCommand cmd)
reparseDecl (RST.DataDecl loc doc decl) =
  RST.DataDecl loc doc decl
reparseDecl (RST.XtorDecl loc doc dc xt args ret) =
  RST.XtorDecl loc doc dc xt args ret
reparseDecl (RST.ImportDecl loc doc mn) =
  RST.ImportDecl loc doc mn
reparseDecl (RST.SetDecl loc doc txt) =
  RST.SetDecl loc doc txt
reparseDecl (RST.TyOpDecl loc doc op prec assoc ty) =
  RST.TyOpDecl loc doc op prec assoc ty

reparseProgram :: RST.Program -> RST.Program
reparseProgram = fmap reparseDecl