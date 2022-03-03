module Translate.Focusing
  ( focusProgram
  , focusTerm
  , focusCmd
  , focusEnvironment
  , isFocusedTerm
  , isFocusedCmd
  ) where

import Data.Text qualified as T

import Syntax.AST.Program ( Declaration(..), Program, Environment(..) )
import Syntax.CommonTerm
    ( FreeVarName,
      PrdCns(Cns, Prd),
      PrdCnsRep(..),
      XtorName,
      Phase(..))
import Syntax.AST.Terms
    ( Command(..),
      Term(..),
      CmdCase(..),
      Substitution,
      commandClosing,
      shiftCmd, PrdCnsTerm(..))
import Syntax.Kinds ( CallingConvention(..), Kind(..) )


---------------------------------------------------------------------------------
-- Check whether terms are focused, values or covalues
---------------------------------------------------------------------------------

-- | Check whether given sterms is substitutable.
isValueTerm :: CallingConvention -> PrdCnsRep pc -> Term pc Compiled -> Maybe (Term pc Compiled)
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

isValuePCTerm :: CallingConvention -> PrdCnsTerm Compiled -> Maybe (PrdCnsTerm Compiled)
isValuePCTerm eo (PrdTerm tm) = PrdTerm <$> isValueTerm eo PrdRep tm
isValuePCTerm eo (CnsTerm tm) = CnsTerm <$> isValueTerm eo CnsRep tm

-- | Check whether all arguments in the given argument list are substitutable.
isValueSubst :: CallingConvention -> Substitution Compiled -> Maybe (Substitution Compiled)
isValueSubst eo subst = sequence (isValuePCTerm eo <$> subst)

-- | Check whether given term follows the focusing discipline.
isFocusedTerm :: CallingConvention -> Term pc Compiled -> Maybe (Term pc Compiled)
isFocusedTerm _  bv@BoundVar {}           = Just bv
isFocusedTerm _  fv@FreeVar {}            = Just fv
isFocusedTerm eo (Xtor _ pc xt subst)     = Xtor () pc xt <$> isValueSubst eo subst
isFocusedTerm eo (XMatch _ x y  cases)    = XMatch () x y <$> (sequence (isFocusedCmdCase eo <$> cases))
isFocusedTerm eo (MuAbs _ pc v cmd)       = MuAbs () pc v <$> isFocusedCmd eo cmd
isFocusedTerm _ _ = error "isFocusedTerm should only be called on core terms."

isFocusedCmdCase :: CallingConvention -> CmdCase Compiled -> Maybe (CmdCase Compiled)
isFocusedCmdCase eo (MkCmdCase _ xt args cmd) = MkCmdCase () xt args <$> isFocusedCmd eo cmd

-- | Check whether given command follows the focusing discipline.
isFocusedCmd :: CallingConvention -> Command Compiled -> Maybe (Command Compiled)
isFocusedCmd eo (Apply _ _ prd cns)    = Apply () (Just (MonoKind eo)) <$> isFocusedTerm eo prd <*> isFocusedTerm eo cns
isFocusedCmd _  (Done _)               = Just (Done ())
isFocusedCmd _  (Call _ fv)            = Just (Call () fv)
isFocusedCmd eo (Print _ prd cmd)      = Print () <$> isValueTerm eo PrdRep prd <*> isFocusedCmd eo cmd
isFocusedCmd eo (Read _ cns)           = Read () <$> isValueTerm eo CnsRep cns

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
-- [[Done]]        := Done
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

focusTerm :: CallingConvention  -> Term pc Compiled -> Term pc Compiled
-- If the term is already focused, we don't want to do anything
focusTerm eo (isFocusedTerm eo -> Just tm) = tm
focusTerm _  (BoundVar _ rep var)          = BoundVar () rep var
focusTerm _  (FreeVar _ rep var)           = FreeVar () rep var
focusTerm eo (Xtor _ pcrep name subst)     = focusXtor eo pcrep name subst
focusTerm eo (XMatch _ rep ns cases)       = XMatch () rep ns (focusCmdCase eo <$> cases)
focusTerm eo (MuAbs _ rep _ cmd)           = MuAbs () rep Nothing (focusCmd eo cmd)
focusTerm _ _                              = error "focusTerm should only be called on Core terms"

-- | The variable used for focusing the entire Xtor.
-- We use an unparseable name to guarantee that the name is fresh.
alphaVar :: FreeVarName
alphaVar = "$alpha"

-- | The variable used for focusing the individual arguments of the Xtor.
-- We use an unparseable name to guarantee that the name is fresh.
betaVar :: Int -> FreeVarName
betaVar i = "$beta" <> T.pack (show i)

-- | Invariant of `focusXtor`:
--   The output should have the property `isFocusedSTerm`.
focusXtor :: CallingConvention -> PrdCnsRep pc -> XtorName -> Substitution Compiled -> Term pc Compiled
focusXtor eo PrdRep name subst = MuAbs () PrdRep Nothing (commandClosing [(Cns, alphaVar)] (shiftCmd (focusXtor' eo PrdRep name subst [])))
focusXtor eo CnsRep name subst = MuAbs () CnsRep Nothing (commandClosing [(Prd, alphaVar)] (shiftCmd (focusXtor' eo CnsRep name subst [])))


focusXtor' :: CallingConvention -> PrdCnsRep pc -> XtorName -> [PrdCnsTerm Compiled] -> [PrdCnsTerm Compiled] -> Command Compiled
focusXtor' eo CnsRep name [] pcterms' = Apply () (Just (MonoKind eo)) (FreeVar () PrdRep alphaVar)
                                                                      (Xtor () CnsRep name (reverse pcterms'))
focusXtor' eo PrdRep name [] pcterms' = Apply () (Just (MonoKind eo)) (Xtor () PrdRep name (reverse pcterms'))
                                                                      (FreeVar () CnsRep alphaVar)
focusXtor' eo pc     name (PrdTerm (isValueTerm eo PrdRep -> Just prd):pcterms) pcterms' = focusXtor' eo pc name pcterms (PrdTerm prd : pcterms')
focusXtor' eo pc     name (PrdTerm                                 prd:pcterms) pcterms' =
                                                              let
                                                                  var = betaVar (length pcterms') -- OK?
                                                                  cmd = commandClosing [(Prd,var)]  (shiftCmd (focusXtor' eo pc name pcterms (PrdTerm (FreeVar () PrdRep var) : pcterms')))
                                                              in
                                                                  Apply () (Just (MonoKind eo)) (focusTerm eo prd) (MuAbs () CnsRep Nothing cmd)
focusXtor' eo pc     name (CnsTerm (isValueTerm eo CnsRep -> Just cns):pcterms) pcterms' = focusXtor' eo pc name pcterms (CnsTerm cns : pcterms')
focusXtor' eo pc     name (CnsTerm                                 cns:pcterms) pcterms' =
                                                              let
                                                                  var = betaVar (length pcterms') -- OK?
                                                                  cmd = commandClosing [(Cns,var)] (shiftCmd (focusXtor' eo pc name pcterms (CnsTerm (FreeVar () CnsRep var) : pcterms')))
                                                              in Apply () (Just (MonoKind eo)) (MuAbs () PrdRep Nothing cmd) (focusTerm eo cns)



focusCmdCase :: CallingConvention -> CmdCase Compiled -> CmdCase Compiled
focusCmdCase eo MkCmdCase { cmdcase_name, cmdcase_args, cmdcase_cmd } =
    MkCmdCase () cmdcase_name ((\(pc,_) -> (pc, Nothing)) <$> cmdcase_args) (focusCmd eo cmdcase_cmd)

-- | Invariant:
-- The output should have the property `isFocusedCmd cmd`.
focusCmd :: CallingConvention -> Command Compiled -> Command Compiled
focusCmd eo (Apply _ _ prd cns) = Apply () (Just (MonoKind eo)) (focusTerm eo prd) (focusTerm eo cns)
focusCmd _  (Done _) = Done ()
focusCmd _  (Call _ fv) = Call () fv
focusCmd eo (Print _ (isValueTerm eo PrdRep -> Just prd) cmd) = Print () prd (focusCmd eo cmd)
focusCmd eo (Print _ prd cmd) = Apply () (Just (MonoKind eo)) (focusTerm eo prd)
                                                              (MuAbs () CnsRep Nothing (Print () (BoundVar () PrdRep (0,0)) (focusCmd eo cmd)))
focusCmd eo (Read _ (isValueTerm eo CnsRep -> Just cns)) = Read () cns
focusCmd eo (Read _ cns) = Apply () (Just (MonoKind eo)) (MuAbs () PrdRep Nothing (Read () (BoundVar () CnsRep (0,0))))
                                                         (focusTerm eo cns)

---------------------------------------------------------------------------------
-- Lift Focusing to programs
---------------------------------------------------------------------------------

focusDecl :: CallingConvention -> Declaration Compiled -> Declaration Compiled
focusDecl eo (PrdCnsDecl _ pc isRec name annot prd) = PrdCnsDecl () pc isRec name annot (focusTerm eo prd)
focusDecl eo (CmdDecl _ name cmd)             = CmdDecl () name (focusCmd eo cmd)
focusDecl _  decl@(DataDecl _ _)              = decl
focusDecl _  decl@(XtorDecl _ _ _ _ _)        = decl
focusDecl _  decl@(ImportDecl _ _)            = decl
focusDecl _  decl@(SetDecl _ _)               = decl

focusProgram :: CallingConvention -> Program Compiled -> Program Compiled
focusProgram eo = fmap (focusDecl eo)

focusEnvironment :: CallingConvention -> Environment Compiled -> Environment Compiled
focusEnvironment cc (MkEnvironment { prdEnv, cnsEnv, cmdEnv, declEnv }) =
    MkEnvironment
      { prdEnv = (\(tm,loc,tys) -> (focusTerm cc tm,loc,tys)) <$> prdEnv
      , cnsEnv = (\(tm,loc,tys) -> (focusTerm cc tm,loc,tys)) <$> cnsEnv
      , cmdEnv = (\(cmd,loc) -> (focusCmd cc cmd,loc)) <$> cmdEnv
      , declEnv = declEnv
      }