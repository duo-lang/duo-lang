module Translate.Reparse
  ( reparseTerm
  , reparseCommand
  , reparseDecl
  , reparseProgram
  ) where

import Control.Monad.State
import Data.Bifunctor
import Data.Text qualified as T

import Syntax.Common
import Syntax.AST.Program
import Syntax.AST.Terms
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

createNamesPCTerm :: PrdCnsTerm -> CreateNameM PrdCnsTerm
createNamesPCTerm (PrdTerm tm) = PrdTerm <$> createNamesTerm tm
createNamesPCTerm (CnsTerm tm) = CnsTerm <$> createNamesTerm tm

createNamesSubstitution :: Substitution  -> CreateNameM Substitution
createNamesSubstitution = mapM createNamesPCTerm

createNamesTerm :: Term pc -> CreateNameM (Term pc)
createNamesTerm (BoundVar loc pc annot idx) =
  pure $ BoundVar loc pc annot idx
createNamesTerm (FreeVar loc pc annot nm) =
  pure $ FreeVar loc pc annot nm
createNamesTerm (Xtor loc pc annot ns xt subst) = do
  subst' <- createNamesSubstitution subst
  pure $ Xtor loc pc annot ns xt subst'
createNamesTerm (XMatch loc pc annot ns cases) = do
  cases' <- mapM createNamesCmdCase cases
  pure $ XMatch loc pc annot ns cases'
createNamesTerm (MuAbs loc pc annot _ cmd) = do
  cmd' <- createNamesCommand cmd
  var <- fresh (case pc of PrdRep -> Cns; CnsRep -> Prd)
  pure $ MuAbs loc pc annot var cmd'
createNamesTerm (Dtor loc pc annot ns xt e (subst1,pcrep,subst2)) = do
  e' <- createNamesTerm e
  subst1' <- createNamesSubstitution subst1
  subst2' <- createNamesSubstitution subst2
  pure $ Dtor loc pc annot ns xt e' (subst1',pcrep,subst2')
createNamesTerm (Case loc annot ns e cases) = do
  e' <- createNamesTerm e
  cases' <- sequence (createNamesTermCase <$> cases)
  pure $ Case loc annot ns e' cases'
createNamesTerm (Cocase loc annot ns cases) = do
  cases' <- sequence (createNamesTermCaseI <$> cases)
  pure $ Cocase loc annot ns cases'
createNamesTerm (PrimLitI64 loc i) =
  pure (PrimLitI64 loc i)
createNamesTerm (PrimLitF64 loc d) =
  pure (PrimLitF64 loc d)

createNamesCommand :: Command -> CreateNameM Command
createNamesCommand (ExitSuccess loc) =
  pure $ ExitSuccess loc
createNamesCommand (ExitFailure loc) =
  pure $ ExitFailure loc
createNamesCommand (Jump loc fv) =
  pure $ Jump loc fv
createNamesCommand (Apply loc kind prd cns) = do
  prd' <- createNamesTerm prd
  cns' <- createNamesTerm cns
  pure $ Apply loc kind prd' cns'
createNamesCommand (Print loc prd cmd) = do
  prd' <- createNamesTerm prd
  cmd' <- createNamesCommand cmd
  pure $ Print loc prd' cmd'
createNamesCommand (Read loc cns) = do
  cns' <- createNamesTerm cns
  pure $ Read loc cns'
createNamesCommand (PrimOp loc pt pop subst) = do
  subst' <- sequence $ createNamesPCTerm <$> subst
  pure $ PrimOp loc pt pop subst'

createNamesCmdCase :: CmdCase -> CreateNameM CmdCase
createNamesCmdCase (MkCmdCase { cmdcase_name, cmdcase_args, cmdcase_cmd }) = do
  cmd' <- createNamesCommand cmdcase_cmd
  args <- sequence $ (\(pc,_) -> (fresh pc >>= \v -> return (pc,v))) <$> cmdcase_args
  return $ MkCmdCase defaultLoc cmdcase_name args cmd'

createNamesTermCase :: TermCase pc -> CreateNameM (TermCase pc)
createNamesTermCase (MkTermCase _ xt args e) = do
  e' <- createNamesTerm e
  args' <- sequence $ (\(pc,_) -> (fresh pc >>= \v -> return (pc,v))) <$> args
  return $ MkTermCase defaultLoc xt args' e'

createNamesTermCaseI :: TermCaseI pc -> CreateNameM (TermCaseI pc)
createNamesTermCaseI (MkTermCaseI _ xt (as1, (), as2) e) = do
  e' <- createNamesTerm e
  let f = (\(pc,_) -> fresh pc >>= \v -> return (pc,v))
  as1' <- sequence $ f <$> as1
  as2' <- sequence $ f <$> as2
  return $ MkTermCaseI defaultLoc xt (as1', (), as2') e'

---------------------------------------------------------------------------------
-- CreateNames Monad
---------------------------------------------------------------------------------

reparseTerm :: Term pc -> Term pc
reparseTerm tm = evalState (createNamesTerm tm) names

reparseCommand :: Command -> Command
reparseCommand cmd = evalState (createNamesCommand cmd) names

reparseDecl :: Declaration -> Declaration
reparseDecl (PrdCnsDecl loc doc rep isRec fv ts tm) =
  PrdCnsDecl loc doc rep isRec fv ts (reparseTerm tm)
reparseDecl (CmdDecl loc doc fv cmd) =
  CmdDecl loc doc fv (reparseCommand cmd)
reparseDecl (DataDecl loc doc decl) =
  DataDecl loc doc decl
reparseDecl (XtorDecl loc doc dc xt args ret) =
  XtorDecl loc doc dc xt args ret
reparseDecl (ImportDecl loc doc mn) =
  ImportDecl loc doc mn
reparseDecl (SetDecl loc doc txt) =
  SetDecl loc doc txt
reparseDecl (TyOpDecl loc doc op prec assoc ty) =
  TyOpDecl loc doc op prec assoc ty

reparseProgram :: Program -> Program
reparseProgram = fmap reparseDecl