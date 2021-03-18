module Syntax.Program where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Foldable (find)
import Syntax.STerms
import Syntax.ATerms
import Syntax.Types

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data Declaration a
  = PrdDecl FreeVarName (STerm Prd a)
  | CnsDecl FreeVarName (STerm Cns a)
  | CmdDecl FreeVarName (Command a)
  | DefDecl FreeVarName (ATerm a)
  | TypDecl TypeName (TypeScheme Pos)
  | DataDecl DataDecl

---------------------------------------------------------------------------------
-- Environment
---------------------------------------------------------------------------------

data Environment = Environment
  { prdEnv :: Map FreeVarName (STerm Prd ())
  , cnsEnv :: Map FreeVarName (STerm Cns ())
  , cmdEnv :: Map FreeVarName (Command ())
  , defEnv :: Map FreeVarName (ATerm ())
  , typEnv :: Map TypeName (TypeScheme Pos)
  , declEnv :: [DataDecl]
  }

instance Semigroup Environment where
  (Environment prdEnv1 cnsEnv1 cmdEnv1 defEnv1 typEnv1 declEnv1) <> (Environment prdEnv2 cnsEnv2 cmdEnv2 defEnv2 typEnv2 declEnv2) =
    Environment { prdEnv = M.union prdEnv1 prdEnv2
                , cnsEnv = M.union cnsEnv1 cnsEnv2
                , cmdEnv = M.union cmdEnv1 cmdEnv2
                , defEnv = M.union defEnv1 defEnv2
                , typEnv = M.union typEnv1 typEnv2
                , declEnv = declEnv1 ++ declEnv2
                }

instance Monoid Environment where
  mempty = Environment
    { prdEnv = M.empty
    , cnsEnv = M.empty
    , cmdEnv = M.empty
    , defEnv = M.empty
    , typEnv = M.empty
    , declEnv = []
    }

envToXtorMap :: Environment -> Map XtorName (TypArgs Pos)
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

    containsXtor :: XtorSig Pos -> Bool
    containsXtor sig = sig_name sig == xt

