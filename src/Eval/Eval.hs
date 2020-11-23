module Eval.Eval
  ( eval
  ) where

import Prettyprinter (Pretty)
import Data.List (find)

import Eval.Substitution
import Pretty
import Syntax.Terms
import Utils

eval :: Pretty a => Command a -> Either Error String
eval Done = Right "Done"
eval (Print t) = Right $ ppPrint t
eval cmd@(Apply (XtorCall Data xt args) (Match Data cases))
  = case (find (\(xt',_,_) -> xt==xt') cases) of
      Just (_,argTypes,cmd') ->
        if fmap length argTypes == fmap length args
          then eval $ commandOpening args cmd' --reduction is just opening
          else Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                 "\"\nArgument lengths don't coincide.")
      Nothing -> Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                   "\"\nXtor \"" ++ xt ++ "\" doesn't occur in match.")
eval cmd@(Apply (Match Codata cases) (XtorCall Codata xt args))
  = case (find (\(xt',_,_) -> xt==xt') cases) of
      Just (_,argTypes,cmd') ->
        if fmap length argTypes == fmap length args
          then eval $ commandOpening args cmd' --reduction is just opening
          else Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                 "\"\nArgument lengths don't coincide.")
      Nothing -> Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                   "\"\nXtor \"" ++ xt ++ "\" doesn't occur in match.")
eval (Apply (MuAbs Cns _ cmd) cns) = eval $ commandOpeningSingle Cns cns cmd
eval (Apply prd (MuAbs Prd _ cmd)) = eval $ commandOpeningSingle Prd prd cmd

-- Error handling
eval cmd@(Apply (XtorCall Codata _ _) _) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                       "\"\nLeft side is not a producer!")
eval cmd@(Apply _ (Match Codata _)) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                       "\"\nRight side is not a consumer!")
eval cmd@(Apply (Match Data _) _) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                       "\"\nLeft side is not a producer!")
eval cmd@(Apply _ (XtorCall Data _ _)) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                       "\"\nRight side is not a consumer!")
eval cmd@(Apply (MuAbs Prd _ _) _) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                       "\"\nLeft side is not a producer!")
eval cmd@(Apply _ (MuAbs Cns _ _)) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                                       "\"\nRight side is not a consumer!")
eval cmd@(Apply _ _) = Left $ EvalError ("Error during evaluation of \"" ++ ppPrint cmd ++
                                          "\"\n Free variable encountered!")

