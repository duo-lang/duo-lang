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
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.CST.Names
import Loc ( Loc, HasLoc(getLoc))

---------------------------------------------------------------------------------
-- Resolved Pattern
-- 
-- These are supposed to end up in src/Syntax/RST/Terms.hs eventually, but they
-- are used as an intermediate step here.
---------------------------------------------------------------------------------

data Pattern where
  PatXtor        :: Loc -> PrdCns -> CST.NominalStructural -> XtorName -> [Pattern] -> Pattern
  PatVar         :: Loc -> PrdCns -> FreeVarName -> Pattern
  PatStar        :: Loc -> PrdCns -> Pattern
  PatWildcard    :: Loc -> PrdCns -> Pattern

instance HasLoc Pattern where
  getLoc :: Pattern -> Loc
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
    (MethodNameResult _cn _) -> do
      throwOtherError loc ["Expected a constructor or destructor, but found a typeclas method."]
    (XtorNameResult dc ns arity) -> do
      when (length arity /= length pats) $
        throwError (ErrResolution (XtorArityMismatch loc xt (length arity) (length pats)) :| [])
      -- Check whether the Xtor is a Constructor/Destructor as expected.
      case (pc,dc) of
        (Cns, CST.Data  ) -> throwOtherError loc ["Expected a destructor but found a constructor"]
        (Prd, CST.Codata) -> throwOtherError loc ["Expected a constructor but found a destructor"]
        (Prd, CST.Data  ) -> pure ()
        (Cns, CST.Codata) -> pure ()
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

analyzePattern :: CST.DataCodata -> CST.Pattern -> ResolverM AnalyzedPattern
analyzePattern dc pat = do
  pat' <- resolvePattern (case dc of CST.Data -> Prd; CST.Codata -> Cns) pat
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


analyzeInstancePattern :: CST.Pattern -> ResolverM (Loc, XtorName, [(Loc, PrdCns, FreeVarName)])
analyzeInstancePattern (CST.PatXtor loc xt pats) = do
  (_,res) <- lookupXtor loc xt
  case res of 
    XtorNameResult {} -> do
      throwOtherError loc ["Expected typeclass method but found xtor" <> T.pack (show xt)]
    MethodNameResult _cn arity -> do
      when (length arity /= length pats) $
        throwError (ErrResolution (XtorArityMismatch loc xt (length arity) (length pats)) :| [])
      pats' <- zipWithM resolvePattern arity pats
      args <- mapM fromVar pats'
      pure (loc, xt, args)
analyzeInstancePattern pat = 
  throwOtherError (getLoc pat) ["Expected typeclass method but found pattern" <> T.pack (show pat)]

