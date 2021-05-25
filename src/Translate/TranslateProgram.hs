module Translate.TranslateProgram 
  (compileProgram)
  where

-- import Data.Map (Map)
-- import qualified Data.Map as M
import Translate.Translate (compile)
import Syntax.Program
-- import Syntax.STerms
-- import Syntax.ATerms
-- import Syntax.Types
-- import Utils

compileProgram :: Program a -> Program a
compileProgram ps = compileDecl <$> ps
  where
    compileDecl :: Declaration a -> Declaration a
    compileDecl (DefDecl isRec loc v t) = PrdDecl isRec loc v $ compile t
    compileDecl decl = decl
