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
    ( throwOtherError,
      ResolutionError(XtorArityMismatch),
      Warning(MisnamedConsumerVar, MisnamedProducerVar),
      Error(ErrResolution) )
import Resolution.Definition ( ResolverM, lookupXtor )
import Resolution.SymbolTable ( XtorNameResolve(..) )
import Syntax.CST.Terms qualified as CST
import Syntax.CST.Types qualified as CST
import Syntax.CST.Types (PrdCns(..), PrdCnsRep(..))
import Syntax.CST.Names ( FreeVarName(MkFreeVarName), XtorName )
import Loc ( Loc, HasLoc(getLoc))
import Data.Either (isRight, fromLeft, fromRight)

---------------------------------------------------------------------------------
-- Resolved Pattern
-- 
-- These are supposed to end up in src/Syntax/RST/Terms.hs eventually, but they
-- are used as an intermediate step here.
---------------------------------------------------------------------------------

data Pattern where
  PatXtor     :: Loc -> PrdCns -> CST.NominalStructural -> XtorName -> [Pattern] -> Pattern
  PatVar      :: Loc -> PrdCns -> FreeVarName -> Pattern
  PatWildcard :: Loc -> PrdCns -> Pattern

deriving instance Eq Pattern
deriving instance Show Pattern

instance HasLoc Pattern where
  getLoc :: Pattern -> Loc
  getLoc (PatXtor loc _ _ _ _) = loc
  getLoc (PatVar loc _ _) = loc
  getLoc (PatWildcard loc _) = loc

data StarPattern where
  PatStar     :: Loc -> PrdCns -> StarPattern
  PatXtorStar :: Loc -> PrdCns -> CST.NominalStructural -> XtorName -> ([Pattern],StarPattern,[Pattern]) -> StarPattern

deriving instance Eq StarPattern
deriving instance Show StarPattern

instance HasLoc StarPattern where
  getLoc :: StarPattern -> Loc
  getLoc (PatStar loc _) = loc
  getLoc (PatXtorStar loc _ _ _ _) = loc

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
resolvePattern :: PrdCns -> CST.Pattern -> ResolverM (Either Pattern StarPattern)
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
        Left pats''' -> pure $ Left (PatXtor loc pc ns xt pats''')
        Right pats''' -> pure $ Right (PatXtorStar loc pc ns xt pats''')
resolvePattern Prd (CST.PatVar loc var@(MkFreeVarName name)) = do
  when ("k" `T.isPrefixOf` name) $
    tell [MisnamedProducerVar loc name]
  pure $ Left (PatVar loc Prd var)
resolvePattern Cns (CST.PatVar loc var@(MkFreeVarName name))  = do
  unless ("k" `T.isPrefixOf` name) $
    tell [MisnamedConsumerVar loc name]
  pure $ Left (PatVar loc Cns var)
resolvePattern pc (CST.PatStar loc) = do
  pure $ Right (PatStar loc pc)
resolvePattern pc (CST.PatWildcard loc) = do
  pure $ Left (PatWildcard loc pc)

---------------------------------------------------------------------------------
-- Analyze Patterns
---------------------------------------------------------------------------------

data AnalyzedPattern
  = ExplicitPattern Loc XtorName [(Loc, PrdCns, FreeVarName)]
  | ImplicitPrdPattern Loc XtorName ([(Loc, PrdCns, FreeVarName)], PrdCnsRep Prd,[(Loc, PrdCns,FreeVarName)])
  | ImplicitCnsPattern Loc XtorName ([(Loc, PrdCns, FreeVarName)], PrdCnsRep Cns,[(Loc, PrdCns,FreeVarName)])


fromVar :: Pattern -> ResolverM (Loc, PrdCns, FreeVarName)
fromVar (PatVar loc pc var) = pure (loc, pc, var)
fromVar pat = throwOtherError (getLoc pat) ["Called function \"fromVar\" on pattern which is not a variable."]


analyzePattern :: CST.DataCodata -> CST.Pattern -> ResolverM AnalyzedPattern
analyzePattern dc pat = do
  pat' <- resolvePattern (case dc of CST.Data -> Prd; CST.Codata -> Cns) pat
  case pat' of
    -- Patterns
    Left (PatXtor loc _pc _ns xt pats) -> do
      vars <- mapM fromVar pats
      pure $ ExplicitPattern loc xt vars
    Left _ -> throwOtherError (getLoc pat) ["Invalid pattern in function \"analyzePattern\""]
    -- StarPatterns
    Right (PatXtorStar loc _pc _ns xt (pats_left,PatStar _ pc,pats_right)) -> do
      pats_left' <- mapM fromVar pats_left
      pats_right' <- mapM fromVar pats_right
      case pc of
        Cns -> pure $ ImplicitPrdPattern loc xt (pats_left', PrdRep, pats_right')
        Prd -> pure $ ImplicitCnsPattern loc xt (pats_left', CnsRep, pats_right')
    Right _ -> throwOtherError (getLoc pat) ["Invalid star pattern in function \"analyzePattern\""]


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

