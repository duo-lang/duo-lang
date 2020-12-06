module Eval.Eval where

import Prettyprinter

import Data.List (find)
import Syntax.Terms
import Eval.Substitution
import Utils
import Pretty


lookupCase :: XtorName -> [Case a] -> Either Error (Case a)
lookupCase xt cases = case find (\MkCase { case_name } -> xt == case_name) cases of
  Just pmcase -> Right pmcase
  Nothing -> Left $ EvalError $ unlines ["Error during evaluation. The xtor: "
                                        , unXtorName xt
                                        , "doesn't occur in match."
                                        ]

eval :: Pretty a => Command a -> Either Error String
eval Done = Right "Done"
eval (Print t) = Right $ ppPrint t
eval cmd@(Apply (XtorCall PrdRep xt args) (Match CnsRep cases)) = do
  (MkCase _ argTypes cmd') <- lookupCase xt cases
  if True -- TODO fmap length argTypes == fmap length args
    then eval $ commandOpening args cmd' --reduction is just opening
    else Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                           "\"\nArgument lengths don't coincide.")
eval cmd@(Apply (Match PrdRep cases) (XtorCall CnsRep xt args)) = do
  (MkCase _ argTypes cmd') <- lookupCase xt cases
  if True -- TODO fmap length argTypes == fmap length args
    then eval $ commandOpening args cmd' --reduction is just opening
    else Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                            "\"\nArgument lengths don't coincide.")
eval (Apply (MuAbs PrdRep _ cmd) cns) = eval $ commandOpeningSingle CnsRep cns cmd
eval (Apply prd (MuAbs CnsRep _ cmd)) = eval $ commandOpeningSingle PrdRep prd cmd
-- Error handling
eval cmd@(Apply _ _) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                          "\"\n Free variable encountered!")
