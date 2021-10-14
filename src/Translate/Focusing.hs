module Translate.Focusing where

import Data.Bifunctor
import Syntax.STerms

---------------------------------------------------------------------------------
-- Check whether terms are focused, values or covalues
---------------------------------------------------------------------------------

-- Check whether terms are values

isValueTermPrd :: STerm Prd ext bs -> Bool
isValueTermPrd BoundVar {}           = True
isValueTermPrd FreeVar {}            = True
isValueTermPrd (XtorCall _ _ _ args) = isValueArgs args
isValueTermPrd (XMatch _ _ _ cases)  = and (isFocusedCase <$> cases)
isValueTermPrd MuAbs {}              = False

isValueTermCns :: STerm Cns ext bs -> Bool
isValueTermCns BoundVar {}           = True
isValueTermCns FreeVar {}            = True
isValueTermCns (XtorCall _ _ _ args) = isValueArgs args
isValueTermCns (XMatch _ _ _ cases)  = and (isFocusedCase <$> cases)
isValueTermCns (MuAbs _ _ _ cmd)     = isFocusedCmd cmd

isValueArgs :: XtorArgs ext bs -> Bool
isValueArgs MkXtorArgs { prdArgs, cnsArgs } = and (valuePrds <> valueCnss)
    where   
        valuePrds = isValueTermPrd <$> prdArgs
        valueCnss = isValueTermCns <$> cnsArgs

-- Check whether terms are focused

isFocusedPrd :: STerm Prd ext bs -> Bool
isFocusedPrd BoundVar {}           = True
isFocusedPrd FreeVar {}            = True
isFocusedPrd (XtorCall _ _ _ args) = isValueArgs args
isFocusedPrd (XMatch _ _ _  cases) = and (isFocusedCase <$> cases)
isFocusedPrd (MuAbs _ _ _ cmd)     = isFocusedCmd cmd

isFocusedCns :: STerm Cns ext bs -> Bool
isFocusedCns BoundVar {}           = True
isFocusedCns FreeVar {}            = True
isFocusedCns (XtorCall _ _ _ args) = isValueArgs args
isFocusedCns (XMatch _ _ _ cases)  = and (isFocusedCase <$> cases)
isFocusedCns (MuAbs _ _ _ cmd)     = isFocusedCmd cmd

isFocusedCmd :: Command ext bs -> Bool
isFocusedCmd (Apply _ prd cns) = isFocusedPrd prd && isFocusedCns cns
isFocusedCmd (Done _)          = True
isFocusedCmd (Print _ prd)     = isFocusedPrd prd

isFocusedCase :: SCase ext bs -> Bool
isFocusedCase MkSCase { scase_cmd } = isFocusedCmd scase_cmd

---------------------------------------------------------------------------------
-- Commands
---------------------------------------------------------------------------------

-- Implement static focusing

focusSTerm :: STerm pc ext bs -> STerm pc () bs
focusSTerm = first (const ())

focusCmd :: Command ext bs -> Command () bs
focusCmd  (Apply _ prd cns) = Apply () (focusSTerm prd) (focusSTerm cns)
focusCmd (Done _) = Done ()
focusCmd (Print _ prd) = Print () (focusSTerm prd) -- TODO Treat similarly to Ctors?

-- focusPrd (Ctor xtor args) = focusCtor xtor args []

-- focusCtor xtor [] args' = Ctor x args'

-- focusCtor xtor (arg:args) = 