module Syntax.Program where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Foldable (find)
import Syntax.STerms
import Syntax.Types
import Utils

---------------------------------------------------------------------------------
-- Program
---------------------------------------------------------------------------------

data Declaration a
  = PrdDecl FreeVarName (STerm Prd a)
  | CnsDecl FreeVarName (STerm Cns a)
  | CmdDecl FreeVarName (Command a)
  | TypDecl TypeName TypeScheme
  | DataDecl DataDecl
  deriving (Show)

data Environment = Environment
  { prdEnv :: Map FreeVarName (STerm Prd ())
  , cnsEnv :: Map FreeVarName (STerm Cns ())
  , cmdEnv :: Map FreeVarName (Command ())
  , typEnv :: Map TypeName TypeScheme
  , declEnv :: [DataDecl]
  }

instance Semigroup Environment where
  (Environment prdEnv1 cnsEnv1 cmdEnv1 typEnv1 declEnv1) <> (Environment prdEnv2 cnsEnv2 cmdEnv2 typEnv2 declEnv2) =
    Environment { prdEnv = M.union prdEnv1 prdEnv2
                , cnsEnv = M.union cnsEnv1 cnsEnv2
                , cmdEnv = M.union cmdEnv1 cmdEnv2
                , typEnv = M.union typEnv1 typEnv2
                , declEnv = declEnv1 ++ declEnv2
                }

instance Monoid Environment where
  mempty = Environment
    { prdEnv = M.empty
    , cnsEnv = M.empty
    , cmdEnv = M.empty
    , typEnv = M.empty
    , declEnv = []
    }

insertDecl :: Declaration () -> Environment -> Environment
insertDecl (PrdDecl v t)  env@Environment { prdEnv }  = env { prdEnv  = M.insert v t prdEnv }
insertDecl (CnsDecl v t)  env@Environment { cnsEnv }  = env { cnsEnv  = M.insert v t cnsEnv }
insertDecl (CmdDecl v t)  env@Environment { cmdEnv }  = env { cmdEnv  = M.insert v t cmdEnv }
insertDecl (TypDecl n t)  env@Environment { typEnv }  = env { typEnv  = M.insert n t typEnv }
insertDecl (DataDecl dcl) env@Environment { declEnv } = env { declEnv = dcl : declEnv }

envToXtorMap :: Environment -> Map XtorName (Twice [SimpleType])
envToXtorMap Environment { declEnv } = M.unions xtorMaps
  where
    xtorMaps = xtorSigsToAssocList <$> declEnv
    xtorSigsToAssocList NominalDecl { data_xtors } =
      M.fromList ((\MkXtorSig { sig_name, sig_args } ->(sig_name, sig_args)) <$> data_xtors)

lookupXtor :: XtorName -> Environment -> Maybe DataDecl
lookupXtor xt Environment { declEnv } = find typeContainsXtor declEnv
  where
    typeContainsXtor :: DataDecl -> Bool
    typeContainsXtor NominalDecl { data_xtors } | or (containsXtor <$> data_xtors) = True
                                   | otherwise = False

    containsXtor :: XtorSig SimpleType -> Bool
    containsXtor sig = sig_name sig == xt

