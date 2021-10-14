module Translate.Focusing where

import Syntax.STerms

-- Implement static focusing


isFocused :: STerm pc ext bs -> Bool
isFocused _tm = True

focusSTerm :: STerm pc ext bs -> STerm pc ext bs
focusSTerm tm = tm

focusCmd :: Command ext bs -> Command ext bs
focusCmd  tm = tm
