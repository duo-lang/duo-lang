module Translate.Focusing where

import qualified Data.Text as T

import Syntax.Program ( Declaration(..), Program )
import Translate.Translate (compileSTerm)
import Syntax.CommonTerm
    ( FreeVarName,
      PrdCns(Cns, Prd),
      PrdCnsRep(..),
      XtorName,
      Phase(..),
      flipPrdCns )
import Syntax.STerms
    ( Command(..),
      STerm(..),
      SCase(..),
      XtorArgs(..),
      commandClosingSingle,
      shiftCmd)
import Syntax.Kinds ( CallingConvention(..) )

---------------------------------------------------------------------------------
-- Check whether terms are focused, values or covalues
---------------------------------------------------------------------------------

-- | Check whether given sterms is substitutable.
isValueSTerm :: CallingConvention -> PrdCnsRep pc -> STerm pc ext -> Bool
isValueSTerm CBV PrdRep MuAbs {}          = False            -- CBV: so Mu is not a value.
isValueSTerm CBV CnsRep (MuAbs _ _ _ cmd) = isFocusedCmd CBV cmd -- CBV: so Mu~ is always a Value.
isValueSTerm CBN PrdRep (MuAbs _ _ _ cmd) = isFocusedCmd CBN cmd -- CBN: so Mu is always a value.
isValueSTerm CBN CnsRep MuAbs {}          = False            -- CBN: So Mu~ is not a value.
isValueSTerm eo  _      tm                = isFocusedSTerm eo tm

-- | Check whether all arguments in the given argument list are substitutable.
isValueArgs :: CallingConvention -> XtorArgs ext -> Bool
isValueArgs eo MkXtorArgs { prdArgs, cnsArgs } = and (valuePrds <> valueCnss)
    where
        valuePrds = isValueSTerm eo PrdRep <$> prdArgs
        valueCnss = isValueSTerm eo CnsRep <$> cnsArgs

-- | Check whether given term follows the focusing discipline.
isFocusedSTerm :: CallingConvention -> STerm pc ext -> Bool
isFocusedSTerm _  BoundVar {}           = True
isFocusedSTerm _  FreeVar {}            = True
isFocusedSTerm eo (XtorCall _ _ _ args) = isValueArgs eo args
isFocusedSTerm eo (XMatch _ _ _  cases) = and (isFocusedCase eo <$> cases)
isFocusedSTerm eo (MuAbs _ _ _ cmd)     = isFocusedCmd eo cmd

isFocusedCase :: CallingConvention -> SCase ext -> Bool
isFocusedCase eo MkSCase { scase_cmd } = isFocusedCmd eo scase_cmd

-- | Check whether given command follows the focusing discipline.
isFocusedCmd :: CallingConvention -> Command ext -> Bool
isFocusedCmd eo (Apply _ prd cns) = isFocusedSTerm eo prd && isFocusedSTerm eo cns
isFocusedCmd _  (Done _)          = True
isFocusedCmd eo (Print _ prd)     = isFocusedSTerm eo prd

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
-- STerms:
--
-- [[x]]                               := x
-- [[(co-)match { X(xs)[ks] => cmd }]] := (co-)match { X(xs)[ks] => [[cmd]] }
-- [[mu x. cmd]]                       := mu x. [[cmd]]
-- [[X(prds)[cnss]]]                   := X(prds)[cnss]                     (if "X(prds)[cnss]" is already focused)
-- [[X(prds)[cnss]]]                   := focusXtor Prd/Cns X prds cnss     (otherwise, see below)
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
-- variable "beta_i" for every term in the argument list which is not a value.
--
-- focusXtor Prd X prds cnss := mu  alpha. (focusXtor' Prd X prds cnss [] [])
-- focusXtor Cns X prds cnss := mu~ alpha. (focusXtor' Cns X prds cnss [] [])
--
-- writing "p" and "P" for unfocused and focused producers, and "c" and "C" for
-- unfocused consumers, the helper function `focusXtor'`  works like this:
-- 
-- If we have transformed all arguments, we reconstruct the constructor application,
-- and apply it to the generated alpha:
--
-- focuxXtor' Prd X [] [] Ps Cs := X(Ps)[Cs] >> alpha
-- focusXtor' Cns X [] [] Ps Cs := alpha >> X(Ps)[Cs]
-- 
-- otherwise, we handle the next prd/cns from the argument list.
-- If the argument is already a value, we shuffle it to the RHS:
--
-- focusXtor' _ _ (P:ps) cs     Ps Cs := focusXtor' _ _ ps cs (P:Ps) Cs
-- focusXtor' _ _ ps     (C:cs) Ps Cs := focusXtor' _ _ ps cs Ps     (C:Cs)
--
-- If the argument is not a value, we have to lift it:
--
-- focusXtor' _ _ (p:ps) cs     Ps Cs := [[p]] >> (mu~ beta_i. focusXtor' _ _ ps cs (beta_i:Ps) Cs)
-- focusXtor' _ _ ps     (c:cs) Ps Cs := (mu beta_i. focusXtor' _ _ ps cs Ps (beta_i:Cs)) >> [[c]]
---------------------------------------------------------------------------------

focusSTerm :: CallingConvention  -> STerm pc ext -> STerm pc Compiled
-- If the term is already focused, we don't want to do anything
focusSTerm eo tm | isFocusedSTerm eo tm                                = compileSTerm tm
focusSTerm _  (BoundVar _ rep var)                                     = BoundVar () rep var
focusSTerm _  (FreeVar _ rep var)                                      = FreeVar () rep var
focusSTerm eo (XtorCall _ pcrep name MkXtorArgs { prdArgs, cnsArgs })  = focusXtor eo pcrep name prdArgs cnsArgs
focusSTerm eo (XMatch _ rep ns cases)                                  = XMatch () rep ns (focusSCase eo <$> cases)
focusSTerm eo (MuAbs _ rep _ cmd)                                      = MuAbs () rep Nothing (focusCmd eo cmd)


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
focusXtor :: CallingConvention -> PrdCnsRep pc -> XtorName -> [STerm Prd ext] -> [STerm Cns ext] -> STerm pc Compiled
focusXtor eo pcrep name prdArgs cnsArgs = MuAbs () pcrep Nothing cmd
  where
      cmd = commandClosingSingle (flipPrdCns pcrep) alphaVar (shiftCmd (focusXtor' eo pcrep name prdArgs cnsArgs [] []))


focusXtor' :: CallingConvention -> PrdCnsRep pc -> XtorName -> [STerm Prd ext] -> [STerm Cns ext] -> [STerm Prd Compiled] -> [STerm Cns Compiled] -> Command Compiled
focusXtor' _  CnsRep name []         []         prd' cns' = Apply () (FreeVar () PrdRep alphaVar) (XtorCall () CnsRep name (MkXtorArgs (reverse prd') (reverse cns')))
focusXtor' _  PrdRep name []         []         prd' cns' = Apply () (XtorCall () PrdRep name (MkXtorArgs (reverse prd') (reverse cns'))) (FreeVar () CnsRep alphaVar)
focusXtor' eo pc     name (prd:prds) cns        prd' cns' | isValueSTerm eo PrdRep prd = focusXtor' eo pc name prds cns (compileSTerm prd : prd') cns'
                                                          | otherwise                   =
                                                              let
                                                                  var = betaVar (length (prd:prds) + length cns)
                                                                  cmd = commandClosingSingle PrdRep var (shiftCmd (focusXtor' eo pc name prds cns (FreeVar () PrdRep var : prd') cns'))
                                                              in
                                                                  Apply () (focusSTerm eo prd) (MuAbs () CnsRep Nothing cmd)
focusXtor' eo pc     name []         (cns:cnss) prd' cns' | isValueSTerm eo CnsRep cns = focusXtor' eo pc name [] cnss prd' (compileSTerm cns : cns')
                                                          | otherwise                   =
                                                              let
                                                                  var = betaVar (length (cns:cnss))
                                                                  cmd = commandClosingSingle CnsRep var (shiftCmd (focusXtor' eo pc name [] cnss prd' (FreeVar () CnsRep var: cns')))
                                                              in Apply () (MuAbs () PrdRep Nothing cmd) (focusSTerm eo cns)



focusSCase :: CallingConvention -> SCase ext -> SCase Compiled
focusSCase eo MkSCase { scase_name, scase_args, scase_cmd } =
    MkSCase scase_name (fmap (const Nothing) <$> scase_args) (focusCmd eo scase_cmd)

-- | Invariant:
-- The output should have the property `isFocusedCmd cmd`.
focusCmd :: CallingConvention -> Command ext -> Command Compiled
focusCmd eo (Apply _ prd cns) = Apply () (focusSTerm eo prd) (focusSTerm eo cns)
focusCmd _  (Done _) = Done ()
-- TODO: Treatment of Print still a bit unclear. Treat similarly to Ctors?
focusCmd eo (Print _ prd) = Print () (focusSTerm eo prd)

---------------------------------------------------------------------------------
-- Lift Focusing to programs
---------------------------------------------------------------------------------

focusDecl :: CallingConvention -> Declaration Compiled -> Declaration Compiled
focusDecl eo (PrdDecl _ isRec name annot prd) = PrdDecl () isRec name annot (focusSTerm eo prd)
focusDecl eo (CnsDecl _ isRec name annot cns) = CnsDecl () isRec name annot (focusSTerm eo cns)
focusDecl eo (CmdDecl _ name cmd)             = CmdDecl () name (focusCmd eo cmd)
focusDecl _  decl@(DefDecl _ _ _ _ _)         = decl
focusDecl _  decl@(DataDecl _ _)              = decl
focusDecl _  decl@(ImportDecl _ _)            = decl
focusDecl _  decl@(SetDecl _ _)               = decl
focusDecl _  decl@ParseErrorDecl              = decl

focusProgram :: CallingConvention -> Program Compiled -> Program Compiled
focusProgram eo = fmap (focusDecl eo)
