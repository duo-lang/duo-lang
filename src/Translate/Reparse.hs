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

createNamesPCTerm :: PrdCnsTerm ext -> CreateNameM (PrdCnsTerm Parsed)
createNamesPCTerm (PrdTerm tm) = PrdTerm <$> createNamesTerm tm
createNamesPCTerm (CnsTerm tm) = CnsTerm <$> createNamesTerm tm

createNamesTerm :: Term pc ext -> CreateNameM (Term pc Parsed)
createNamesTerm (BoundVar _ pc idx) = return $ BoundVar defaultLoc pc idx
createNamesTerm (FreeVar _ pc nm)   = return $ FreeVar defaultLoc pc nm
createNamesTerm (Xtor _ pc ns xt subst) = do
  subst' <- sequence $ createNamesPCTerm <$> subst
  return $ Xtor defaultLoc pc ns xt subst'
createNamesTerm (XMatch _ pc ns cases) = do
  cases' <- sequence $ createNamesCmdCase <$> cases
  return $ XMatch defaultLoc pc ns cases'
createNamesTerm (MuAbs _ pc _ cmd) = do
  cmd' <- createNamesCommand cmd
  var <- fresh (case pc of PrdRep -> Cns; CnsRep -> Prd)
  return $ MuAbs defaultLoc pc var cmd'
createNamesTerm (Dtor _ ns xt e (args1,pcrep,args2)) = do
  e' <- createNamesTerm e
  args1' <- sequence (createNamesPCTerm <$> args1)
  args2' <- sequence (createNamesPCTerm <$> args2)
  return $ Dtor defaultLoc ns xt e' (args1',pcrep,args2')
createNamesTerm (Case _ ns e cases) = do
  e' <- createNamesTerm e
  cases' <- sequence (createNamesTermCase <$> cases)
  return $ Case defaultLoc ns e' cases'
createNamesTerm (Cocase _ ns cases) = do
  cases' <- sequence (createNamesTermCaseI <$> cases)
  return $ Cocase defaultLoc ns cases'
createNamesTerm (PrimLit _ lit) = pure (PrimLit defaultLoc lit)

createNamesCommand :: Command ext -> CreateNameM (Command Parsed)
createNamesCommand (Done _) = return $ Done defaultLoc
createNamesCommand (Call _ fv) = return $ Call defaultLoc fv
createNamesCommand (Apply _ kind prd cns) = do
  prd' <- createNamesTerm prd
  cns' <- createNamesTerm cns
  return (Apply defaultLoc kind prd' cns')
createNamesCommand (Print _ prd cmd) = do
  prd' <- createNamesTerm prd
  cmd' <- createNamesCommand cmd
  return (Print defaultLoc prd' cmd')
createNamesCommand (Read _ cns) = do
  cns' <- createNamesTerm cns
  return (Read defaultLoc cns')
createNamesCommand (PrimOp _ pt pop subst) = do
  subst' <- sequence $ createNamesPCTerm <$> subst
  return (PrimOp defaultLoc pt pop subst')

createNamesCmdCase :: CmdCase ext -> CreateNameM (CmdCase Parsed)
createNamesCmdCase (MkCmdCase { cmdcase_name, cmdcase_args, cmdcase_cmd }) = do
  cmd' <- createNamesCommand cmdcase_cmd
  args <- sequence $ (\(pc,_) -> (fresh pc >>= \v -> return (pc,v))) <$> cmdcase_args
  return $ MkCmdCase defaultLoc cmdcase_name args cmd'

createNamesTermCase :: TermCase ext -> CreateNameM (TermCase Parsed)
createNamesTermCase (MkTermCase _ xt args e) = do
  e' <- createNamesTerm e
  args' <- sequence $ (\(pc,_) -> (fresh pc >>= \v -> return (pc,v))) <$> args
  return $ MkTermCase defaultLoc xt args' e'

createNamesTermCaseI :: TermCaseI ext -> CreateNameM (TermCaseI Parsed)
createNamesTermCaseI (MkTermCaseI _ xt (as1, (), as2) e) = do
  e' <- createNamesTerm e
  let f = (\(pc,_) -> fresh pc >>= \v -> return (pc,v))
  as1' <- sequence $ f <$> as1
  as2' <- sequence $ f <$> as2
  return $ MkTermCaseI defaultLoc xt (as1', (), as2') e'

---------------------------------------------------------------------------------
-- CreateNames Monad
---------------------------------------------------------------------------------

reparseTerm :: Term pc ext -> Term pc Parsed
reparseTerm tm = evalState (createNamesTerm tm) names

reparseCommand :: Command ext -> Command Parsed
reparseCommand cmd = evalState (createNamesCommand cmd) names

reparseDecl :: Declaration ext -> Declaration Parsed
reparseDecl (PrdCnsDecl _ rep isRec fv ts tm) = PrdCnsDecl (Nothing, defaultLoc) rep isRec fv ts (reparseTerm tm)
reparseDecl (CmdDecl _ fv cmd)                = CmdDecl (Nothing, defaultLoc) fv (reparseCommand cmd)
reparseDecl (DataDecl _ decl)                 = DataDecl (Nothing, defaultLoc) decl
reparseDecl (XtorDecl _ dc xt args ret)       = XtorDecl (Nothing, defaultLoc) dc xt args ret
reparseDecl (ImportDecl _ mn)                 = ImportDecl (Nothing, defaultLoc) mn
reparseDecl (SetDecl _ txt)                   = SetDecl (Nothing, defaultLoc) txt
reparseDecl (TyOpDecl _ op prec assoc ty)     = TyOpDecl (Nothing, defaultLoc) op prec assoc ty

reparseProgram :: Program ext -> Program Parsed
reparseProgram = fmap reparseDecl