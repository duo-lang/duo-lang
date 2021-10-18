module Translate.Focusing where

import qualified Data.Text as T
import Control.Monad ( void )
import Data.Bifunctor
import Syntax.STerms

---------------------------------------------------------------------------------
-- Check whether terms are focused, values or covalues
---------------------------------------------------------------------------------

-- Check whether terms are values

isValueTermPrd :: STerm Prd ext bs -> Bool
isValueTermPrd MuAbs {} = False -- Hard coded CBV, so Mu is not a value.
isValueTermPrd tm       = isFocusedPrd tm

isValueTermCns :: STerm Cns ext bs -> Bool
isValueTermCns (MuAbs _ _ _ cmd)  = isFocusedCmd cmd -- Hard coded CBV, so Mu~ is always a Value.
isValueTermCns tm                 = isFocusedCns tm

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
-- The Focusing Algorithm
---------------------------------------------------------------------------------

alphaVar :: FreeVarName 
alphaVar = "$alpha" -- Use unparseable name to guarantee freshness.

betaVar :: Int -> FreeVarName
betaVar i = "$beta" <> T.pack (show i)

focusSTerm :: STerm pc ext bs -> STerm pc () ()
focusSTerm (BoundVar _ rep var)                                     = BoundVar () rep var
focusSTerm (FreeVar _ rep var)                                      = FreeVar () rep var
focusSTerm (XtorCall _ PrdRep name MkXtorArgs { prdArgs, cnsArgs }) = focusCtor name prdArgs cnsArgs
focusSTerm (XtorCall _ CnsRep name MkXtorArgs { prdArgs, cnsArgs }) = focusDtor name prdArgs cnsArgs
focusSTerm (XMatch _ rep ns cases)                                  = XMatch () rep ns (focusSCase <$> cases)
focusSTerm (MuAbs _ rep _ cmd)                                      = MuAbs () rep () (focusCmd cmd)

-- | Invariant of `focusCtor`:
--   The output should have the property `isFocusedPrd`.
focusCtor :: XtorName -> [STerm Prd ext bs] -> [STerm Cns ext bs] -> STerm Prd () ()
focusCtor name prdArgs cnsArgs = MuAbs () PrdRep () cmd
  where
      cmd = commandClosingSingle CnsRep alphaVar (focusXtor Prd name prdArgs cnsArgs [] [])

focusDtor :: XtorName -> [STerm Prd ext bs] -> [STerm Cns ext bs] -> STerm Cns () ()
focusDtor name prdArgs cnsArgs = MuAbs () CnsRep () cmd 
  where
      cmd = commandClosingSingle PrdRep alphaVar (focusXtor Cns name prdArgs cnsArgs [] [])


focusXtor :: PrdCns -> XtorName -> [STerm Prd ext bs] -> [STerm Cns ext bs] -> [STerm Prd () ()] -> [STerm Cns () ()] -> Command () ()
focusXtor Cns name []         []         prd' cns' = Apply () (FreeVar () PrdRep alphaVar) (XtorCall () CnsRep name (MkXtorArgs (reverse prd') (reverse cns')))
focusXtor Prd name []         []         prd' cns' = Apply () (XtorCall () PrdRep name (MkXtorArgs (reverse prd') (reverse cns'))) (FreeVar () CnsRep alphaVar)
focusXtor pc  name (prd:prds) cns        prd' cns' | isValueTermPrd prd = focusXtor pc name prds cns (bimap (const ()) (const ()) prd : prd') cns'
                                                   | otherwise          = 
                                                       let
                                                           var = betaVar (length (prd:prds) + length cns)
                                                           cmd = commandClosingSingle PrdRep var (focusXtor pc name prds cns (FreeVar () PrdRep var : prd') cns')
                                                       in
                                                           Apply () (focusSTerm prd) (MuAbs () CnsRep () cmd)
focusXtor pc  name []         (cns:cnss) prd' cns' | isValueTermCns cns = focusXtor pc name [] cnss prd' (bimap (const ()) (const ()) cns : cns')
                                                   | otherwise          = 
                                                       let 
                                                           var = betaVar (length (cns:cnss))
                                                           cmd = commandClosingSingle CnsRep var (focusXtor pc name [] cnss prd' (FreeVar () CnsRep var: cns'))
                                                       in Apply () (MuAbs () PrdRep () cmd) (focusSTerm cns)



focusSCase :: SCase ext bs -> SCase () ()
focusSCase MkSCase { scase_name, scase_args, scase_cmd } =
    MkSCase scase_name (void <$> scase_args) (focusCmd scase_cmd)

focusCmd :: Command ext bs -> Command () ()
focusCmd  (Apply _ prd cns) | isFocusedPrd prd && isFocusedCns cns = Apply () (bimap (const ()) (const ()) prd) (bimap (const ()) (const ()) cns)
                            | isFocusedPrd prd = Apply () (bimap (const ()) (const ()) prd) (focusSTerm cns)
                            | isFocusedCns cns = Apply () (focusSTerm prd) (bimap (const ()) (const ()) cns)
                            | otherwise = Apply () (focusSTerm prd) (focusSTerm cns)
focusCmd (Done _) = Done ()
-- TODO: Treatment of Print still a bit unclear. Treat similarly to Ctors?
focusCmd (Print _ prd) | isFocusedPrd prd = Print () (bimap (const ()) (const ())  prd)
                       | otherwise = Print () (focusSTerm prd)
