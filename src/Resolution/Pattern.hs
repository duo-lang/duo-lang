module Resolution.Pattern
  ( AnalyzedPattern(..)
  , analyzePattern
  , analyzeInstancePattern
  ) where

import Control.Monad ( unless, when, zipWithM )
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Writer ( MonadWriter(tell) )
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Text qualified as T

import Errors
import Resolution.Definition ( ResolverM, lookupXtor )
import Resolution.SymbolTable ( XtorNameResolve(..) )
import Syntax.CST.Terms qualified as CST
import Syntax.Common.PrdCns
import Syntax.Common.Names
import Syntax.Common.Types
import Syntax.Common.XData
import Utils ( Loc, HasLoc(getLoc))

---------------------------------------------------------------------------------
-- Resolved Pattern
-- 
-- These are supposed to end up in src/Syntax/RST/Terms.hs eventually, but they
-- are used as an intermediate step here.
---------------------------------------------------------------------------------

data Pattern where
  PatClassMethod :: Loc -> XtorName -> [(Loc, PrdCns, FreeVarName)] -> Pattern
  PatXtor        :: Loc -> PrdCns -> NominalStructural -> XtorName -> [Pattern] -> Pattern
  PatVar         :: Loc -> PrdCns -> FreeVarName -> Pattern
  PatStar        :: Loc -> PrdCns -> Pattern
  PatWildcard    :: Loc -> PrdCns -> Pattern

instance HasLoc Pattern where
  getLoc (PatClassMethod loc _ _) = loc
  getLoc (PatXtor loc _ _ _ _) = loc
  getLoc (PatVar loc _ _) = loc
  getLoc (PatStar loc _) = loc
  getLoc (PatWildcard loc _) = loc

---------------------------------------------------------------------------------
-- Resolve Pattern
---------------------------------------------------------------------------------

-- | Annotate every part of the pattern with information on whether it stands for
-- a producer or consumer.
resolvePattern :: PrdCns -> CST.Pattern -> ResolverM Pattern
resolvePattern pc (CST.PatXtor loc xt pats) = do
  -- Lookup up the arity information in the symbol table.
  (_,res) <- lookupXtor loc xt
  case res of
    (MethodNameResult _cn arity) -> do
      when (length arity /= length pats) $
        throwError (ErrResolution (XtorArityMismatch loc xt (length arity) (length pats)) :| [])
      pats' <- zipWithM resolvePattern arity pats
      args <- mapM fromVar pats'
      pure $ PatClassMethod loc xt args
    (XtorNameResult dc ns arity) -> do
      when (length arity /= length pats) $
        throwError (ErrResolution (XtorArityMismatch loc xt (length arity) (length pats)) :| [])
      -- Check whether the Xtor is a Constructor/Destructor as expected.
      case (pc,dc) of
        (Cns, Data  ) -> throwOtherError loc ["Expected a destructor but found a constructor"]
        (Prd, Codata) -> throwOtherError loc ["Expected a constructor but found a destructor"]
        (Prd, Data  ) -> pure ()
        (Cns, Codata) -> pure ()
      pats' <- zipWithM resolvePattern arity pats
      pure (PatXtor loc pc ns xt pats')
resolvePattern Prd (CST.PatVar loc var@(MkFreeVarName name)) = do
  when ("k" `T.isPrefixOf` name) $
    tell [MisnamedProducerVar loc name]
  pure $ PatVar loc Prd var
resolvePattern Cns (CST.PatVar loc var@(MkFreeVarName name))  = do
  unless ("k" `T.isPrefixOf` name) $
    tell [MisnamedConsumerVar loc name]
  pure $ PatVar loc Cns var
resolvePattern pc (CST.PatStar loc) = do
  pure $ PatStar loc pc
resolvePattern pc (CST.PatWildcard loc) = do
  pure $ PatWildcard loc pc

---------------------------------------------------------------------------------
-- Analyze Patterns
---------------------------------------------------------------------------------

data AnalyzedPattern
  = ExplicitPattern Loc XtorName [(Loc, PrdCns, FreeVarName)]
  | ImplicitPrdPattern Loc XtorName ([(Loc, PrdCns, FreeVarName)], PrdCnsRep Prd,[(Loc, PrdCns,FreeVarName)])
  | ImplicitCnsPattern Loc XtorName ([(Loc, PrdCns, FreeVarName)], PrdCnsRep Cns,[(Loc, PrdCns,FreeVarName)])

isStar :: Pattern -> Bool
isStar (PatStar _ _) = True
isStar _ = False

fromVar :: Pattern -> ResolverM (Loc, PrdCns, FreeVarName)
fromVar (PatVar loc pc var) = pure (loc, pc, var)
fromVar pat = throwOtherError (getLoc pat) ["Called function \"fromVar\" on pattern which is not a variable."]

analyzePattern :: DataCodata -> CST.Pattern -> ResolverM AnalyzedPattern
analyzePattern dc pat = do
  pat' <- resolvePattern (case dc of Data -> Prd; Codata -> Cns) pat
  case pat' of
    PatXtor loc _pc _ns xt pats -> do
      case length (filter isStar pats) of
        0 -> do
          vars <- sequence (fromVar <$> pats)
          pure $ ExplicitPattern loc xt vars
        1 -> do
          case break isStar pats of
            (args1,PatStar _ pc:args2) -> do
              args1' <- sequence (fromVar <$> args1)
              args2' <- sequence (fromVar <$> args2)
              case pc of
                Cns -> pure $ ImplicitPrdPattern loc xt (args1', PrdRep, args2')
                Prd -> pure $ ImplicitCnsPattern loc xt (args1', CnsRep, args2')
            (_,_) -> throwOtherError loc ["Not reachable, since number \"1\" was returned in the check."]
        n -> throwError $ ErrResolution (InvalidStar loc ("More than one star used in binding site: " <> T.pack (show n) <> " stars used.")) :| []
    _ -> throwOtherError (getLoc pat) ["Invalid pattern in function \"analyzePattern\""]


analyzeInstancePattern :: CST.Pattern -> ResolverM AnalyzedPattern
analyzeInstancePattern pat = do
  pat' <- resolvePattern Prd pat
  case pat' of
    PatClassMethod loc xt args -> pure $ ExplicitPattern loc xt args
    _ -> throwOtherError (getLoc pat) ["Expected method but found pattern."]
