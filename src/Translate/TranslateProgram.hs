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
import Data.Bifunctor

compileProgram :: Program a b -> Program () ()
compileProgram ps = compileDecl <$> ps
  where
    compileDecl :: Declaration a b -> Declaration () ()
    compileDecl (DefDecl isRec b v t) = PrdDecl isRec () v $ compile t
	
    compileDecl (PrdDecl isRec b v t) = PrdDecl isRec () v $ bimap (const ()) (const ()) t
    compileDecl (CnsDecl isRec b v t) = CnsDecl isRec () v $ bimap (const ()) (const ()) t
    compileDecl (CmdDecl b v cmd) = CmdDecl () v $ bimap (const ()) (const ()) cmd
    compileDecl (DataDecl b decl) = DataDecl () decl





-- data Declaration a b
  -- = PrdDecl IsRec b FreeVarName (STerm Prd b a)
  -- | CnsDecl IsRec b FreeVarName (STerm Cns b a)
  -- | CmdDecl b FreeVarName (Command b a)
  -- | DefDecl IsRec b FreeVarName (ATerm b a)
  -- | DataDecl b DataDecl