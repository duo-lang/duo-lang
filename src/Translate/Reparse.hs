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
import Syntax.AST.Program qualified as AST
import Syntax.AST.Terms qualified as AST
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

createNamesPCTerm :: AST.PrdCnsTerm -> CreateNameM AST.PrdCnsTerm
createNamesPCTerm (AST.PrdTerm tm) = AST.PrdTerm <$> createNamesTerm tm
createNamesPCTerm (AST.CnsTerm tm) = AST.CnsTerm <$> createNamesTerm tm

createNamesSubstitution :: AST.Substitution  -> CreateNameM AST.Substitution
createNamesSubstitution = mapM createNamesPCTerm

createNamesTerm :: AST.Term pc -> CreateNameM (AST.Term pc)
createNamesTerm (AST.BoundVar loc pc annot idx) =
  pure $ AST.BoundVar loc pc annot idx
createNamesTerm (AST.FreeVar loc pc annot nm) =
  pure $ AST.FreeVar loc pc annot nm
createNamesTerm (AST.Xtor loc pc annot ns xt subst) = do
  subst' <- createNamesSubstitution subst
  pure $ AST.Xtor loc pc annot ns xt subst'
createNamesTerm (AST.XMatch loc pc annot ns cases) = do
  cases' <- mapM createNamesCmdCase cases
  pure $ AST.XMatch loc pc annot ns cases'
createNamesTerm (AST.MuAbs loc pc annot _ cmd) = do
  cmd' <- createNamesCommand cmd
  var <- fresh (case pc of PrdRep -> Cns; CnsRep -> Prd)
  pure $ AST.MuAbs loc pc annot var cmd'
createNamesTerm (AST.Dtor loc pc annot ns xt e (subst1,pcrep,subst2)) = do
  e' <- createNamesTerm e
  subst1' <- createNamesSubstitution subst1
  subst2' <- createNamesSubstitution subst2
  pure $ AST.Dtor loc pc annot ns xt e' (subst1',pcrep,subst2')
createNamesTerm (AST.Case loc annot ns e cases) = do
  e' <- createNamesTerm e
  cases' <- sequence (createNamesTermCase <$> cases)
  pure $ AST.Case loc annot ns e' cases'
createNamesTerm (AST.Cocase loc annot ns cases) = do
  cases' <- sequence (createNamesTermCaseI <$> cases)
  pure $ AST.Cocase loc annot ns cases'
createNamesTerm (AST.PrimLitI64 loc i) =
  pure (AST.PrimLitI64 loc i)
createNamesTerm (AST.PrimLitF64 loc d) =
  pure (AST.PrimLitF64 loc d)

createNamesCommand :: AST.Command -> CreateNameM AST.Command
createNamesCommand (AST.ExitSuccess loc) =
  pure $ AST.ExitSuccess loc
createNamesCommand (AST.ExitFailure loc) =
  pure $ AST.ExitFailure loc
createNamesCommand (AST.Jump loc fv) =
  pure $ AST.Jump loc fv
createNamesCommand (AST.Apply loc kind prd cns) = do
  prd' <- createNamesTerm prd
  cns' <- createNamesTerm cns
  pure $ AST.Apply loc kind prd' cns'
createNamesCommand (AST.Print loc prd cmd) = do
  prd' <- createNamesTerm prd
  cmd' <- createNamesCommand cmd
  pure $ AST.Print loc prd' cmd'
createNamesCommand (AST.Read loc cns) = do
  cns' <- createNamesTerm cns
  pure $ AST.Read loc cns'
createNamesCommand (AST.PrimOp loc pt pop subst) = do
  subst' <- sequence $ createNamesPCTerm <$> subst
  pure $ AST.PrimOp loc pt pop subst'

createNamesCmdCase :: AST.CmdCase -> CreateNameM AST.CmdCase
createNamesCmdCase (AST.MkCmdCase { cmdcase_name, cmdcase_args, cmdcase_cmd }) = do
  cmd' <- createNamesCommand cmdcase_cmd
  args <- sequence $ (\(pc,_) -> (fresh pc >>= \v -> return (pc,v))) <$> cmdcase_args
  return $ AST.MkCmdCase defaultLoc cmdcase_name args cmd'

createNamesTermCase :: AST.TermCase pc -> CreateNameM (AST.TermCase pc)
createNamesTermCase (AST.MkTermCase _ xt args e) = do
  e' <- createNamesTerm e
  args' <- sequence $ (\(pc,_) -> (fresh pc >>= \v -> return (pc,v))) <$> args
  return $ AST.MkTermCase defaultLoc xt args' e'

createNamesTermCaseI :: AST.TermCaseI pc -> CreateNameM (AST.TermCaseI pc)
createNamesTermCaseI (AST.MkTermCaseI _ xt (as1, (), as2) e) = do
  e' <- createNamesTerm e
  let f = (\(pc,_) -> fresh pc >>= \v -> return (pc,v))
  as1' <- sequence $ f <$> as1
  as2' <- sequence $ f <$> as2
  return $ AST.MkTermCaseI defaultLoc xt (as1', (), as2') e'

---------------------------------------------------------------------------------
-- CreateNames Monad
---------------------------------------------------------------------------------

reparseTerm :: AST.Term pc -> AST.Term pc
reparseTerm tm = evalState (createNamesTerm tm) names

reparseCommand :: AST.Command -> AST.Command
reparseCommand cmd = evalState (createNamesCommand cmd) names

reparseDecl :: AST.Declaration -> AST.Declaration
reparseDecl (AST.PrdCnsDecl loc doc rep isRec fv ts tm) =
  AST.PrdCnsDecl loc doc rep isRec fv ts (reparseTerm tm)
reparseDecl (AST.CmdDecl loc doc fv cmd) =
  AST.CmdDecl loc doc fv (reparseCommand cmd)
reparseDecl (AST.DataDecl loc doc decl) =
  AST.DataDecl loc doc decl
reparseDecl (AST.XtorDecl loc doc dc xt args ret) =
  AST.XtorDecl loc doc dc xt args ret
reparseDecl (AST.ImportDecl loc doc mn) =
  AST.ImportDecl loc doc mn
reparseDecl (AST.SetDecl loc doc txt) =
  AST.SetDecl loc doc txt
reparseDecl (AST.TyOpDecl loc doc op prec assoc ty) =
  AST.TyOpDecl loc doc op prec assoc ty

reparseProgram :: AST.Program -> AST.Program
reparseProgram = fmap reparseDecl