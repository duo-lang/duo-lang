module Translate.Focusing
  ( focusProgram
  , focusTerm
  , focusCmd
  , focusEnvironment
  , isFocusedTerm
  , isFocusedCmd
  ) where

import Data.Text qualified as T

import Driver.Environment (Environment(..))
import Syntax.AST.Program ( Declaration(..), Program )
import Syntax.Common
import Syntax.AST.Terms
    ( Command(..),
      Term(..),
      CmdCase(..),
      Substitution,
      commandClosing,
      shiftCmd, PrdCnsTerm(..))

---------------------------------------------------------------------------------
-- Check whether terms are focused, values or covalues
---------------------------------------------------------------------------------

-- | Check whether given sterms is substitutable.
isValueTerm :: EvaluationOrder -> PrdCnsRep pc -> Term pc -> Maybe (Term pc)
isValueTerm CBV PrdRep FreeVar {}        = Nothing
isValueTerm CBN PrdRep fv@(FreeVar {})   = Just fv
isValueTerm CBV CnsRep fv@(FreeVar {})   = Just fv
isValueTerm CBN CnsRep (FreeVar {})      = Nothing
isValueTerm CBV PrdRep MuAbs {}          = Nothing              -- CBV: so Mu is not a value.
isValueTerm CBV CnsRep (MuAbs _ pc v cmd) = do
    cmd' <- isFocusedCmd CBV cmd -- CBV: so Mu~ is always a Value.
    return $ MuAbs () pc v cmd'
isValueTerm CBN PrdRep (MuAbs _ pc v cmd) = do
    cmd' <- isFocusedCmd CBN cmd -- CBN: so Mu is always a value.
    return $ MuAbs () pc v cmd'
isValueTerm CBN CnsRep MuAbs {}          = Nothing              -- CBN: So Mu~ is not a value.
isValueTerm eo  _      tm                = isFocusedTerm eo tm

isValuePCTerm :: EvaluationOrder -> PrdCnsTerm -> Maybe PrdCnsTerm
isValuePCTerm eo (PrdTerm tm) = PrdTerm <$> isValueTerm eo PrdRep tm
isValuePCTerm eo (CnsTerm tm) = CnsTerm <$> isValueTerm eo CnsRep tm

-- | Check whether all arguments in the given argument list are substitutable.
isValueSubst :: EvaluationOrder -> Substitution -> Maybe Substitution
isValueSubst eo subst = sequence (isValuePCTerm eo <$> subst)

-- | Check whether given term follows the focusing discipline.
isFocusedTerm :: EvaluationOrder -> Term pc -> Maybe (Term pc)
isFocusedTerm _  bv@BoundVar {}           = Just bv
isFocusedTerm _  fv@FreeVar {}            = Just fv
isFocusedTerm eo (Xtor _ pc ns xt subst)  = Xtor () pc ns xt <$> isValueSubst eo subst
isFocusedTerm eo (XMatch _ x y  cases)    = XMatch () x y <$> (sequence (isFocusedCmdCase eo <$> cases))
isFocusedTerm eo (MuAbs _ pc v cmd)       = MuAbs () pc v <$> isFocusedCmd eo cmd
isFocusedTerm _  lit@PrimLitI64{}         = Just lit
isFocusedTerm _  lit@PrimLitF64{}         = Just lit
isFocusedTerm _  _ = error "isFocusedTerm should only be called on core terms."

isFocusedCmdCase :: EvaluationOrder -> CmdCase -> Maybe CmdCase
isFocusedCmdCase eo (MkCmdCase _ xt args cmd) = MkCmdCase () xt args <$> isFocusedCmd eo cmd

-- | Check whether given command follows the focusing discipline.
isFocusedCmd :: EvaluationOrder -> Command -> Maybe Command
isFocusedCmd eo (Apply _ _ prd cns)    = Apply () (Just (CBox eo)) <$> isFocusedTerm eo prd <*> isFocusedTerm eo cns
isFocusedCmd _  (ExitSuccess _)        = Just (ExitSuccess ())
isFocusedCmd _  (ExitFailure _)        = Just (ExitFailure ())
isFocusedCmd _  (Jump _ fv)            = Just (Jump () fv)
isFocusedCmd eo (Print _ prd cmd)      = Print () <$> isValueTerm eo PrdRep prd <*> isFocusedCmd eo cmd
isFocusedCmd eo (Read _ cns)           = Read () <$> isValueTerm eo CnsRep cns
isFocusedCmd eo (PrimOp _ pt op subst) = PrimOp () pt op <$> isValueSubst eo subst

---------------------------------------------------------------------------------
-- The Focusing Algorithm
--
-- This focusing algorithm is similar to the algorithm presented in Figure 3.19
-- and 3.20 of the PhD thesis of Paul Downen, but generalized to work for arbitrary
-- data and codata types, and multiple evaluation orders.
-- Some optimizations are used to prevent the generation of excessive administrative
-- redexes.
--
-- We write [[t]] for the focusing translation of the term t.
--
-- Terms:
--
-- [[x]]                               := x
-- [[(co-)match { X Gamma => cmd }]]   := (co-)match { X Gamma => [[cmd]] }
-- [[mu x. cmd]]                       := mu x. [[cmd]]
-- [[X subst]]                         := X subst                           (if "X subst" is already focused)
-- [[X subst]]                         := focusXtor Prd/Cns X subst         (otherwise, see below)
--
-- Commands:
--
-- [[prd >> cns]]  := [[prd]] >> [[cns]]
-- [[ExitSuccess]] := ExitSuccess
-- [[ExitFailure]] := ExitFailure
-- [[Print(prd)]]  := ??? Unsure!
--
-- The `focusXtor` and `focusXtor'` function work together to focus a
-- xtor which has arguments which are not substitutable. We generate 1
-- fresh variable "alpha" for the entire term, and one additional fresh
-- variable "beta_i" for every term in the substitution which is not a value.
--
-- focusXtor Prd X subst := mu  alpha. (focusXtor' Prd X subst [])
-- focusXtor Cns X subst := mu~ alpha. (focusXtor' Cns X subst [])
--
-- writing "t" and "T" for unfocused and focused terms, the helper function
-- `focusXtor'`  works like this:
--
-- If we have transformed all arguments, we reconstruct the constructor application,
-- and apply it to the generated alpha:
--
-- focuxXtor' Prd X [] Ts := X Ts >> alpha
-- focusXtor' Cns X [] Ts := alpha >> X Ts
--
-- otherwise, we handle the next term from the substitution.
-- If the argument is already a value, we shuffle it to the RHS:
--
-- focusXtor' _ _ (T:ts) Ts := focusXtor' _ _ ts (T:Ts)
--
-- If the argument is not a value, we have to lift it:
--
-- focusXtor' _ _ (p:ts) Ts := [[p]] >> (mu~ beta_i. focusXtor' _ _ ts (beta_i:Ts))
-- focusXtor' _ _ (c:ts) Ts := (mu beta_i. focusXtor' _ _ ts (beta_i:Ts)) >> [[c]]
---------------------------------------------------------------------------------

focusTerm :: EvaluationOrder  -> Term pc -> Term pc
-- If the term is already focused, we don't want to do anything
focusTerm eo (isFocusedTerm eo -> Just tm) = tm
focusTerm _  (BoundVar _ rep var)          = BoundVar () rep var
focusTerm _  (FreeVar _ rep var)           = FreeVar () rep var
focusTerm eo (Xtor _ pcrep ns xt subst)    = focusXtor eo pcrep ns xt subst
focusTerm eo (XMatch _ rep ns cases)       = XMatch () rep ns (focusCmdCase eo <$> cases)
focusTerm eo (MuAbs _ rep _ cmd)           = MuAbs () rep Nothing (focusCmd eo cmd)
focusTerm _ _                              = error "focusTerm should only be called on Core terms"

-- | The variable used for focusing the entire Xtor.
-- We use an unparseable name to guarantee that the name is fresh.
alphaVar :: FreeVarName
alphaVar = MkFreeVarName "$alpha"

-- | The variable used for focusing the individual arguments of the Xtor.
-- We use an unparseable name to guarantee that the name is fresh.
betaVar :: Int -> FreeVarName
betaVar i = MkFreeVarName ("$beta" <> T.pack (show i))

-- | Invariant of `focusXtor`:
--   The output should have the property `isFocusedSTerm`.
focusXtor :: EvaluationOrder -> PrdCnsRep pc -> NominalStructural -> XtorName -> Substitution -> Term pc
focusXtor eo PrdRep ns xt subst = MuAbs () PrdRep Nothing (commandClosing [(Cns, alphaVar)] (shiftCmd (focusXtor' eo PrdRep ns xt subst [])))
focusXtor eo CnsRep ns xt subst = MuAbs () CnsRep Nothing (commandClosing [(Prd, alphaVar)] (shiftCmd (focusXtor' eo CnsRep ns xt subst [])))


focusXtor' :: EvaluationOrder -> PrdCnsRep pc -> NominalStructural -> XtorName -> [PrdCnsTerm] -> [PrdCnsTerm] -> Command
focusXtor' eo CnsRep ns xt [] pcterms' = Apply () (Just (CBox eo)) (FreeVar () PrdRep alphaVar)
                                                                   (Xtor () CnsRep ns xt (reverse pcterms'))
focusXtor' eo PrdRep ns xt [] pcterms' = Apply () (Just (CBox eo)) (Xtor () PrdRep ns xt (reverse pcterms'))
                                                                   (FreeVar () CnsRep alphaVar)
focusXtor' eo pc     ns xt (PrdTerm (isValueTerm eo PrdRep -> Just prd):pcterms) pcterms' = focusXtor' eo pc ns xt pcterms (PrdTerm prd : pcterms')
focusXtor' eo pc     ns xt (PrdTerm                                 prd:pcterms) pcterms' =
                                                              let
                                                                  var = betaVar (length pcterms') -- OK?
                                                                  cmd = commandClosing [(Prd,var)]  (shiftCmd (focusXtor' eo pc ns xt pcterms (PrdTerm (FreeVar () PrdRep var) : pcterms')))
                                                              in
                                                                  Apply () (Just (CBox eo)) (focusTerm eo prd) (MuAbs () CnsRep Nothing cmd)
focusXtor' eo pc     ns xt (CnsTerm (isValueTerm eo CnsRep -> Just cns):pcterms) pcterms' = focusXtor' eo pc ns xt pcterms (CnsTerm cns : pcterms')
focusXtor' eo pc     ns xt (CnsTerm                                 cns:pcterms) pcterms' =
                                                              let
                                                                  var = betaVar (length pcterms') -- OK?
                                                                  cmd = commandClosing [(Cns,var)] (shiftCmd (focusXtor' eo pc ns xt pcterms (CnsTerm (FreeVar () CnsRep var) : pcterms')))
                                                              in Apply () (Just (CBox eo)) (MuAbs () PrdRep Nothing cmd) (focusTerm eo cns)



focusCmdCase :: EvaluationOrder -> CmdCase -> CmdCase
focusCmdCase eo MkCmdCase { cmdcase_name, cmdcase_args, cmdcase_cmd } =
    MkCmdCase () cmdcase_name ((\(pc,_) -> (pc, Nothing)) <$> cmdcase_args) (focusCmd eo cmdcase_cmd)


focusPrimOp :: EvaluationOrder -> (PrimitiveType, PrimitiveOp) -> [PrdCnsTerm] -> [PrdCnsTerm] -> Command
focusPrimOp _  (pt, op) [] pcterms' = PrimOp () pt op (reverse pcterms')
focusPrimOp eo op (PrdTerm (isValueTerm eo PrdRep -> Just prd):pcterms) pcterms' = focusPrimOp eo op pcterms (PrdTerm prd : pcterms')
focusPrimOp eo op (PrdTerm prd:pcterms) pcterms' =
    let
        var = betaVar (length pcterms')
        cmd = commandClosing [(Prd,var)]  (shiftCmd (focusPrimOp eo op pcterms (PrdTerm (FreeVar () PrdRep var) : pcterms')))
    in
        Apply () (Just (CBox eo)) (focusTerm eo prd) (MuAbs () CnsRep Nothing cmd)
focusPrimOp eo op (CnsTerm (isValueTerm eo CnsRep -> Just cns):pcterms) pcterms' = focusPrimOp eo op pcterms (CnsTerm cns : pcterms')
focusPrimOp eo op (CnsTerm cns:pcterms) pcterms' =
    let
        var = betaVar (length pcterms')
        cmd = commandClosing [(Cns,var)] (shiftCmd (focusPrimOp eo op pcterms (CnsTerm (FreeVar () CnsRep var) : pcterms')))
    in
        Apply () (Just (CBox eo)) (MuAbs () PrdRep Nothing cmd) (focusTerm eo cns)

-- | Invariant:
-- The output should have the property `isFocusedCmd cmd`.
focusCmd :: EvaluationOrder -> Command -> Command
focusCmd eo (Apply _ _ prd cns) = Apply () (Just (CBox eo)) (focusTerm eo prd) (focusTerm eo cns)
focusCmd _  (ExitSuccess _) = ExitSuccess ()
focusCmd _  (ExitFailure _) = ExitFailure ()
focusCmd _  (Jump _ fv) = Jump () fv
focusCmd eo (Print _ (isValueTerm eo PrdRep -> Just prd) cmd) = Print () prd (focusCmd eo cmd)
focusCmd eo (Print _ prd cmd) = Apply () (Just (CBox eo)) (focusTerm eo prd)
                                                          (MuAbs () CnsRep Nothing (Print () (BoundVar () PrdRep (0,0)) (focusCmd eo cmd)))
focusCmd eo (Read _ (isValueTerm eo CnsRep -> Just cns)) = Read () cns
focusCmd eo (Read _ cns) = Apply () (Just (CBox eo)) (MuAbs () PrdRep Nothing (Read () (BoundVar () CnsRep (0,0))))
                                                     (focusTerm eo cns)
focusCmd eo (PrimOp _ pt op subst) = focusPrimOp eo (pt, op) subst []

---------------------------------------------------------------------------------
-- Lift Focusing to programs
---------------------------------------------------------------------------------

focusDecl :: EvaluationOrder -> Declaration -> Declaration
focusDecl eo (PrdCnsDecl _ pc isRec name annot prd) = PrdCnsDecl () pc isRec name annot (focusTerm eo prd)
focusDecl eo (CmdDecl _ name cmd)             = CmdDecl () name (focusCmd eo cmd)
focusDecl _  decl@DataDecl {}                 = decl
focusDecl _  decl@XtorDecl {}                 = decl
focusDecl _  decl@ImportDecl {}               = decl
focusDecl _  decl@SetDecl {}                  = decl
focusDecl _  decl@TyOpDecl {}                 = decl

focusProgram :: EvaluationOrder -> Program -> Program
focusProgram eo = fmap (focusDecl eo)

focusEnvironment :: EvaluationOrder -> Environment -> Environment
focusEnvironment cc (MkEnvironment { prdEnv, cnsEnv, cmdEnv, declEnv }) =
    MkEnvironment
      { prdEnv = (\(tm,loc,tys) -> (focusTerm cc tm,loc,tys)) <$> prdEnv
      , cnsEnv = (\(tm,loc,tys) -> (focusTerm cc tm,loc,tys)) <$> cnsEnv
      , cmdEnv = (\(cmd,loc) -> (focusCmd cc cmd,loc)) <$> cmdEnv
      , declEnv = declEnv
      }
