module Syntax.Program where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Foldable (find)
import Syntax.STerms
import Syntax.ATerms
import Syntax.Types
import Utils

---------------------------------------------------------------------------------
-- Declarations
---------------------------------------------------------------------------------

data Declaration a
  = PrdDecl Loc FreeVarName (STerm Prd () a)
  | CnsDecl Loc FreeVarName (STerm Cns () a)
  | CmdDecl Loc FreeVarName (Command () a)
  | DefDecl Loc FreeVarName (ATerm Loc a)
  | DataDecl Loc DataDecl

instance Show (Declaration a) where
  show _ = "<Show for Declaration not implemented>"

---------------------------------------------------------------------------------
-- Environment
---------------------------------------------------------------------------------

data Environment bs = Environment
  { prdEnv :: Map FreeVarName (STerm Prd () bs, TypeScheme Pos)
  , cnsEnv :: Map FreeVarName (STerm Cns () bs, TypeScheme Neg)
  , cmdEnv :: Map FreeVarName (Command () bs)
  , defEnv :: Map FreeVarName (ATerm () bs, TypeScheme Pos)
  , declEnv :: [DataDecl]
  }

instance Show (Environment bs) where
  show _ = "<Environment>"

instance Semigroup (Environment bs) where
  (Environment prdEnv1 cnsEnv1 cmdEnv1 defEnv1 declEnv1) <> (Environment prdEnv2 cnsEnv2 cmdEnv2 defEnv2 declEnv2) =
    Environment { prdEnv = M.union prdEnv1 prdEnv2
                , cnsEnv = M.union cnsEnv1 cnsEnv2
                , cmdEnv = M.union cmdEnv1 cmdEnv2
                , defEnv = M.union defEnv1 defEnv2
                , declEnv = declEnv1 ++ declEnv2
                }

instance Monoid (Environment bs) where
  mempty = Environment
    { prdEnv = M.empty
    , cnsEnv = M.empty
    , cmdEnv = M.empty
    , defEnv = M.empty
    , declEnv = []
    }

envToXtorMap :: Environment bs -> Map XtorName (TypArgs Pos)
envToXtorMap Environment { declEnv } = M.unions xtorMaps
  where
    xtorMaps = xtorSigsToAssocList <$> declEnv
    xtorSigsToAssocList NominalDecl { data_xtors } =
      M.fromList ((\MkXtorSig { sig_name, sig_args } ->(sig_name, sig_args)) <$> data_xtors)

lookupXtor :: XtorName -> Environment bs -> Maybe DataDecl
lookupXtor xt Environment { declEnv } = find typeContainsXtor declEnv
  where
    typeContainsXtor :: DataDecl -> Bool
    typeContainsXtor NominalDecl { data_xtors } | or (containsXtor <$> data_xtors) = True
                                   | otherwise = False

    containsXtor :: XtorSig Pos -> Bool
    containsXtor sig = sig_name sig == xt

