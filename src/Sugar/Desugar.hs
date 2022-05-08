module Sugar.Desugar
  ( desugarTerm
  , desugarPCTerm
  , desugarProgram
  , desugarCmd
  , desugarEnvironment
  , isDesugaredTerm
  , isDesugaredCommand
  )
  where

import Data.Foldable (fold)
import Data.Map (Map)
import Data.Map qualified as M
import Driver.Environment (Environment(..))
import Eval.Definition (EvalEnv)
import Syntax.AST.Program qualified as AST
import Syntax.AST.Terms qualified as AST
import Syntax.Core.Program qualified as Core
import Syntax.Core.Terms qualified as Core
import Syntax.Common
import qualified Sugar.Core as Core


---------------------------------------------------------------------------------
-- Check if term is desugared
---------------------------------------------------------------------------------

isDesugaredPCTerm :: AST.PrdCnsTerm -> Bool
isDesugaredPCTerm (AST.PrdTerm tm) = isDesugaredTerm tm
isDesugaredPCTerm (AST.CnsTerm tm) = isDesugaredTerm tm

isDesugaredTerm :: AST.Term pc -> Bool
-- Core terms
isDesugaredTerm AST.BoundVar {} = True
isDesugaredTerm AST.FreeVar {} = True
isDesugaredTerm (AST.Xtor _ _ _ _ _ _ subst) =
  and (isDesugaredPCTerm <$> subst)
isDesugaredTerm (AST.MuAbs _ _ _ _ _ cmd) =
  isDesugaredCommand cmd
isDesugaredTerm (AST.XCase _ _ _ _ _ cases) =
  and ((\AST.MkCmdCase { cmdcase_cmd } -> isDesugaredCommand cmdcase_cmd ) <$> cases)
isDesugaredTerm AST.PrimLitI64{} = True
isDesugaredTerm AST.PrimLitF64{} = True
-- Non-core terms
isDesugaredTerm AST.Dtor{} = False
isDesugaredTerm AST.CaseOf {} = False
isDesugaredTerm AST.CocaseOf {} = False
isDesugaredTerm AST.CaseI {} = False
isDesugaredTerm AST.CocaseI {} = False
isDesugaredTerm AST.Semi {} = False


isDesugaredCommand :: AST.Command -> Bool
isDesugaredCommand (AST.Apply _ _ _ prd cns) =
  isDesugaredTerm prd && isDesugaredTerm cns
isDesugaredCommand (AST.Print _ prd cmd) =
  isDesugaredTerm prd && isDesugaredCommand cmd
isDesugaredCommand (AST.Read _ cns) =
  isDesugaredTerm cns
isDesugaredCommand (AST.Jump _ _) = True
isDesugaredCommand (AST.ExitSuccess _) = True
isDesugaredCommand (AST.ExitFailure _) = True
isDesugaredCommand (AST.PrimOp _ _ _ subst) =
  and (isDesugaredPCTerm <$> subst)
isDesugaredCommand AST.CaseOfCmd {} =  False
isDesugaredCommand AST.CaseOfI {} =  False
isDesugaredCommand AST.CocaseOfCmd {} =  False
isDesugaredCommand AST.CocaseOfI {} =  False

---------------------------------------------------------------------------------
-- Desugar Terms
--
-- This translates terms into the core subset of terms.
---------------------------------------------------------------------------------

resVar :: FreeVarName
resVar = MkFreeVarName "$result"

desugarPCTerm :: AST.PrdCnsTerm -> Core.PrdCnsTerm
desugarPCTerm (AST.PrdTerm tm) = Core.PrdTerm $ desugarTerm tm
desugarPCTerm (AST.CnsTerm tm) = Core.CnsTerm $ desugarTerm tm

desugarPat :: AST.Pattern -> Core.Pattern
desugarPat (AST.XtorPat loc xt args) = Core.XtorPat loc xt args

desugarTerm :: AST.Term pc -> Core.Term pc
---------------------------------------------------------------------------------
-- Core constructs
---------------------------------------------------------------------------------
desugarTerm (AST.BoundVar loc pc _ty idx) =
  Core.BoundVar loc pc idx
desugarTerm (AST.FreeVar loc pc _ty fv) =
  Core.FreeVar loc pc fv
desugarTerm (AST.Xtor loc annot pc _ty ns xt args) =
  Core.Xtor loc annot pc ns xt (desugarPCTerm <$> args)
desugarTerm (AST.MuAbs loc annot pc _ty bs cmd) =
  Core.MuAbs loc annot pc bs (desugarCmd cmd)
desugarTerm (AST.XCase loc annot pc _ty ns cases) =
  Core.XCase loc annot pc ns (desugarCmdCase <$> cases)
---------------------------------------------------------------------------------
-- Syntactic sugar
---------------------------------------------------------------------------------
desugarTerm (AST.Semi loc rep _ ns xt (args1,r,args2) t) = Core.Semi loc rep ns xt (desugarPCTerm <$> args1,r,desugarPCTerm <$> args2) (desugarTerm t)
desugarTerm (AST.Dtor loc rep _ ns xt t (args1,r,args2)) = Core.Dtor loc rep ns xt (desugarTerm t) (desugarPCTerm <$> args1,r,desugarPCTerm <$> args2)
desugarTerm (AST.CaseOf loc rep _ ns t cases) = Core.CaseOf loc rep ns (desugarTerm t) (desugarTermCase <$> cases)
desugarTerm (AST.CocaseOf loc rep _ ns t cases) = Core.CocaseOf loc rep ns (desugarTerm t) (desugarTermCase <$> cases)
desugarTerm (AST.CaseI loc rep _ ns tmcasesI) = Core.CaseI loc rep ns (desugarTermCaseI <$> tmcasesI)
desugarTerm (AST.CocaseI loc rep _ ns cocases) = Core.CocaseI loc rep ns (desugarTermCaseI <$> cocases)

---------------------------------------------------------------------------------
-- Primitive constructs
---------------------------------------------------------------------------------
desugarTerm (AST.PrimLitI64 loc i) =
  Core.PrimLitI64 loc i
desugarTerm (AST.PrimLitF64 loc d) =
  Core.PrimLitF64 loc d

desugarCmdCase :: AST.CmdCase -> Core.CmdCase
desugarCmdCase (AST.MkCmdCase loc pat cmd) =
  Core.MkCmdCase loc (desugarPat pat) (desugarCmd cmd)

desugarTermCaseI :: AST.TermCaseI pc -> Core.TermCaseI pc 
desugarTermCaseI (AST.MkTermCaseI loc pti t) = Core.MkTermCaseI loc (desugarPatI pti) (desugarTerm t)

desugarPatI :: AST.PatternI -> Core.PatternI 
desugarPatI (AST.XtorPatI loc xt args) = Core.XtorPatI loc xt args

desugarTermCase :: AST.TermCase pc -> Core.TermCase pc 
desugarTermCase (AST.MkTermCase loc pat t) = Core.MkTermCase loc (desugarPat pat) (desugarTerm t)

desugarCmd :: AST.Command -> Core.Command
desugarCmd (AST.Apply loc annot kind prd cns) =
  Core.Apply loc annot kind (desugarTerm prd) (desugarTerm cns)
desugarCmd (AST.Print loc prd cmd) =
  Core.Print loc (desugarTerm prd) (desugarCmd cmd)
desugarCmd (AST.Read loc cns) =
  Core.Read loc (desugarTerm cns)
desugarCmd (AST.Jump loc fv) =
  Core.Jump loc fv
desugarCmd (AST.ExitSuccess loc) =
  Core.ExitSuccess loc
desugarCmd (AST.ExitFailure loc) =
  Core.ExitFailure loc
desugarCmd (AST.PrimOp loc pt op subst) =
  Core.PrimOp loc pt op (desugarPCTerm <$> subst)
---------------------------------------------------------------------------------
-- Syntactic sugar
-- uses pattern synonyms defined in Sugar.Core 
---------------------------------------------------------------------------------

desugarCmd (AST.CaseOfCmd loc ns t cases) =
  Core.CaseOfCmd loc ns (desugarTerm t) (desugarCmdCase <$> cases) 
desugarCmd (AST.CocaseOfCmd loc ns t cases) =
  Core.CocaseOfCmd loc ns (desugarTerm t) (desugarCmdCase <$> cases) 
desugarCmd (AST.CaseOfI loc rep ns t cases) = 
  Core.CaseOfI loc rep ns (desugarTerm t) (desugarTermCaseI  <$> cases )
desugarCmd (AST.CocaseOfI loc rep ns t cases) = 
  Core.CocaseOfI loc rep ns (desugarTerm t) (desugarTermCaseI  <$> cases )

---------------------------------------------------------------------------------
-- Translate Program
---------------------------------------------------------------------------------

desugarDecl :: AST.Declaration -> Core.Declaration
desugarDecl (AST.PrdCnsDecl loc doc pc isRec fv annot tm) =
  Core.PrdCnsDecl loc doc pc isRec fv annot (desugarTerm tm)
desugarDecl (AST.CmdDecl loc doc fv cmd) =
  Core.CmdDecl loc doc fv (desugarCmd cmd)
desugarDecl (AST.DataDecl loc doc decl) =
  Core.DataDecl loc doc decl
desugarDecl (AST.XtorDecl loc doc dc xt args ret) =
  Core.XtorDecl loc doc dc xt args ret
desugarDecl (AST.ImportDecl loc doc mn) =
  Core.ImportDecl loc doc mn
desugarDecl (AST.SetDecl loc doc txt) =
  Core.SetDecl loc doc txt
desugarDecl (AST.TyOpDecl loc doc op prec assoc ty) =
  Core.TyOpDecl loc doc op prec assoc ty
desugarDecl (AST.TySynDecl loc doc nm ty) = 
  Core.TySynDecl loc doc nm ty

desugarProgram :: AST.Program -> Core.Program
desugarProgram ps = desugarDecl <$> ps

desugarEnvironment :: Map ModuleName Environment -> EvalEnv
desugarEnvironment map = fold $ desugarEnvironment' <$> M.elems map


desugarEnvironment' :: Environment -> EvalEnv
desugarEnvironment' (MkEnvironment { prdEnv, cnsEnv, cmdEnv }) = (prd,cns,cmd)
  where
    prd = (\(tm,_,_) -> (desugarTerm tm)) <$> prdEnv
    cns = (\(tm,_,_) -> (desugarTerm tm)) <$> cnsEnv
    cmd = (\(cmd,_) -> (desugarCmd cmd)) <$> cmdEnv
