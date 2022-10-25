module Resolution.Pattern
  ( resolvePattern
  , fromVar
  , analyzeInstancePattern
  ) where

import Control.Monad ( unless, when, zipWithM )
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Writer ( MonadWriter(tell) )
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Text qualified as T

import Errors
    ( throwOtherError,
      ResolutionError(XtorArityMismatch),
      Warning(MisnamedConsumerVar, MisnamedProducerVar),
      Error(ErrResolution) )
import Resolution.Definition ( ResolverM, lookupXtor )
import Resolution.SymbolTable ( XtorNameResolve(..) )
import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCns(..))
import Syntax.CST.Names ( FreeVarName(MkFreeVarName), XtorName )
import Loc ( Loc, HasLoc(getLoc))
import Syntax.RST.Terms qualified as RST
import Data.Either (isRight, fromLeft, fromRight)

---------------------------------------------------------------------------------
-- Resolve Pattern
---------------------------------------------------------------------------------

findAtMostOneRight :: HasLoc b => [Either a b] -> ResolverM (Either [a] ([a],b,[a]))
findAtMostOneRight args = case break isRight args of
  (pats, []) -> pure $ Left (fromLeft undefined <$> pats)
  (left_pats, (starpat: right_pats)) ->
    case break isRight right_pats of
      (right_pats, []) -> pure $ Right (fromLeft undefined <$> left_pats,fromRight undefined starpat,fromLeft undefined <$> right_pats)
      (_, _:_) -> throwOtherError (getLoc (fromRight undefined starpat)) ["Found more than one star in pattern"]
      
    

-- | Annotate every part of the pattern with information on whether it stands for
-- a producer or consumer.
resolvePattern :: PrdCns -> CST.Pattern -> ResolverM (Either RST.PatternNew RST.StarPattern)
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
      pats'' <- findAtMostOneRight pats'
      case pats'' of
        Left pats''' -> pure $ Left (RST.PatXtor loc pc ns xt pats''')
        Right pats''' -> pure $ Right (RST.PatXtorStar loc pc ns xt pats''')
resolvePattern Prd (CST.PatVar loc var@(MkFreeVarName name)) = do
  when ("k" `T.isPrefixOf` name) $
    tell [MisnamedProducerVar loc name]
  pure $ Left (RST.PatVar loc Prd var)
resolvePattern Cns (CST.PatVar loc var@(MkFreeVarName name))  = do
  unless ("k" `T.isPrefixOf` name) $
    tell [MisnamedConsumerVar loc name]
  pure $ Left (RST.PatVar loc Cns var)
resolvePattern pc (CST.PatStar loc) = do
  pure $ Right (RST.PatStar loc pc)
resolvePattern pc (CST.PatWildcard loc) = do
  pure $ Left (RST.PatWildcard loc pc)

---------------------------------------------------------------------------------
-- Analyze Patterns
---------------------------------------------------------------------------------

fromVar :: RST.PatternNew -> ResolverM (Loc, PrdCns, FreeVarName)
fromVar (RST.PatVar loc pc var) = pure (loc, pc, var)
fromVar (RST.PatWildcard loc pc) = pure (loc, pc, MkFreeVarName "_")
fromVar pat = throwOtherError (getLoc pat) ["Called function \"fromVar\" on pattern which is not a variable."]

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
      foo <- findAtMostOneRight pats'
      case foo of
        Left pats2 -> do
          args <- mapM fromVar pats2
          pure (loc, xt, args)
        Right _ ->
          throwOtherError loc ["Found star in instance method"]
analyzeInstancePattern pat =
  throwOtherError (getLoc pat) ["Expected typeclass method but found pattern" <> T.pack (show pat)]

