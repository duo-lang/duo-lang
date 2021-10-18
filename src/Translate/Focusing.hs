module Translate.Focusing where


import Control.Monad ( void )
import Data.Bifunctor ( Bifunctor(bimap) )
import qualified Data.Text as T

import Syntax.Program ( Declaration(..), Program )
import Syntax.CommonTerm
    ( FreeVarName,
      PrdCns(Cns, Prd),
      PrdCnsRep(..),
      XtorName,
      flipPrdCns )
import Syntax.STerms
    ( Command(..),
      STerm(..),
      SCase(..),
      XtorArgs(..),
      commandClosingSingle )

---------------------------------------------------------------------------------
-- Check whether terms are focused, values or covalues
---------------------------------------------------------------------------------

-- | Check whether given sterms is substitutable.
isValueSTerm :: PrdCnsRep pc -> STerm pc ext bs -> Bool
isValueSTerm PrdRep MuAbs {}          = False            -- Hard coded CBV, so Mu is not a value.
isValueSTerm CnsRep (MuAbs _ _ _ cmd) = isFocusedCmd cmd -- Hard coded CBV, so Mu~ is always a Value.
isValueSTerm _      tm                = isFocusedSTerm tm

-- | Check whether all arguments in the given argument list are substitutable.
isValueArgs :: XtorArgs ext bs -> Bool
isValueArgs MkXtorArgs { prdArgs, cnsArgs } = and (valuePrds <> valueCnss)
    where
        valuePrds = isValueSTerm PrdRep <$> prdArgs
        valueCnss = isValueSTerm CnsRep <$> cnsArgs

-- | Check whether given term follows the focusing discipline.
isFocusedSTerm :: STerm pc ext bs -> Bool
isFocusedSTerm BoundVar {}           = True
isFocusedSTerm FreeVar {}            = True
isFocusedSTerm (XtorCall _ _ _ args) = isValueArgs args
isFocusedSTerm (XMatch _ _ _  cases) = and (isFocusedCase <$> cases)
isFocusedSTerm (MuAbs _ _ _ cmd)     = isFocusedCmd cmd

isFocusedCase :: SCase ext bs -> Bool
isFocusedCase MkSCase { scase_cmd } = isFocusedCmd scase_cmd

-- | Check whether given command follows the focusing discipline.
isFocusedCmd :: Command ext bs -> Bool
isFocusedCmd (Apply _ prd cns) = isFocusedSTerm prd && isFocusedSTerm cns
isFocusedCmd (Done _)          = True
isFocusedCmd (Print _ prd)     = isFocusedSTerm prd

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
---------------------------------------------------------------------------------

alphaVar :: FreeVarName 
alphaVar = "$alpha" -- Use unparseable name to guarantee freshness.

betaVar :: Int -> FreeVarName
betaVar i = "$beta" <> T.pack (show i)

focusSTerm :: PrdCnsRep pc -> STerm pc ext bs -> STerm pc () ()
-- If the term is already focused, we don't want to do anything
focusSTerm PrdRep tm | isFocusedSTerm tm                              = bimap (const ()) (const ()) tm
focusSTerm CnsRep tm | isFocusedSTerm tm                              = bimap (const ()) (const ()) tm
focusSTerm _ (BoundVar _ rep var)                                     = BoundVar () rep var
focusSTerm _ (FreeVar _ rep var)                                      = FreeVar () rep var
focusSTerm _ (XtorCall _ pcrep name MkXtorArgs { prdArgs, cnsArgs })  = focusXtor pcrep name prdArgs cnsArgs
focusSTerm _ (XMatch _ rep ns cases)                                  = XMatch () rep ns (focusSCase <$> cases)
focusSTerm _ (MuAbs _ rep _ cmd)                                      = MuAbs () rep () (focusCmd cmd)

-- | Invariant of `focusXtor`:
--   The output should have the property `isFocusedSTerm`.
focusXtor :: PrdCnsRep pc -> XtorName -> [STerm Prd ext bs] -> [STerm Cns ext bs] -> STerm pc () ()
focusXtor pcrep name prdArgs cnsArgs = MuAbs () pcrep () cmd
  where
      cmd = commandClosingSingle (flipPrdCns pcrep) alphaVar (focusXtor' pcrep name prdArgs cnsArgs [] [])



focusXtor' :: PrdCnsRep pc -> XtorName -> [STerm Prd ext bs] -> [STerm Cns ext bs] -> [STerm Prd () ()] -> [STerm Cns () ()] -> Command () ()
focusXtor' CnsRep name []         []         prd' cns' = Apply () (FreeVar () PrdRep alphaVar) (XtorCall () CnsRep name (MkXtorArgs (reverse prd') (reverse cns')))
focusXtor' PrdRep name []         []         prd' cns' = Apply () (XtorCall () PrdRep name (MkXtorArgs (reverse prd') (reverse cns'))) (FreeVar () CnsRep alphaVar)
focusXtor' pc  name (prd:prds) cns        prd' cns' | isValueSTerm PrdRep prd = focusXtor' pc name prds cns (bimap (const ()) (const ()) prd : prd') cns'
                                                   | otherwise               = 
                                                       let
                                                           var = betaVar (length (prd:prds) + length cns)
                                                           cmd = commandClosingSingle PrdRep var (focusXtor' pc name prds cns (FreeVar () PrdRep var : prd') cns')
                                                       in
                                                           Apply () (focusSTerm PrdRep prd) (MuAbs () CnsRep () cmd)
focusXtor' pc  name []         (cns:cnss) prd' cns' | isValueSTerm CnsRep cns = focusXtor' pc name [] cnss prd' (bimap (const ()) (const ()) cns : cns')
                                                   | otherwise               = 
                                                       let 
                                                           var = betaVar (length (cns:cnss))
                                                           cmd = commandClosingSingle CnsRep var (focusXtor' pc name [] cnss prd' (FreeVar () CnsRep var: cns'))
                                                       in Apply () (MuAbs () PrdRep () cmd) (focusSTerm CnsRep cns)



focusSCase :: SCase ext bs -> SCase () ()
focusSCase MkSCase { scase_name, scase_args, scase_cmd } =
    MkSCase scase_name (void <$> scase_args) (focusCmd scase_cmd)

-- | Invariant:
-- The output should have the property `isFocusedCmd cmd`.
focusCmd :: Command ext bs -> Command () ()
focusCmd  (Apply _ prd cns) = Apply () (focusSTerm PrdRep prd) (focusSTerm CnsRep cns)
focusCmd (Done _) = Done ()
-- TODO: Treatment of Print still a bit unclear. Treat similarly to Ctors?
focusCmd (Print _ prd) = Print () (focusSTerm PrdRep prd)

---------------------------------------------------------------------------------
-- Lift Focusing to programs
---------------------------------------------------------------------------------

focusDecl :: Declaration () () -> Declaration () ()
focusDecl (PrdDecl isRec _ name annot prd) = PrdDecl isRec () name annot (focusSTerm PrdRep prd)
focusDecl (CnsDecl isRec _ name annot cns) = CnsDecl isRec () name annot (focusSTerm CnsRep cns)
focusDecl (CmdDecl _ name cmd)             = CmdDecl () name (focusCmd cmd)
focusDecl decl@(DefDecl _ _ _ _ _)         = decl
focusDecl decl@(DataDecl _ _)              = decl
focusDecl decl@(ImportDecl _ _)            = decl
focusDecl decl@(SetDecl _ _)               = decl
focusDecl decl@ParseErrorDecl              = decl

focusProgram :: Program () () -> Program () ()
focusProgram = fmap focusDecl
