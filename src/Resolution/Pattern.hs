module Resolution.Pattern where

import Control.Monad ( unless, when )
import Control.Monad.Except ( MonadError(throwError) )
import Control.Monad.Writer ( MonadWriter(tell) )
import Data.Bifunctor ( Bifunctor(second) )
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Text qualified as T

import Errors
import Resolution.Definition ( ResolverM, lookupXtor )
import Resolution.SymbolTable ( XtorNameResolve(..) )
import Syntax.Common
import Syntax.CST.Terms qualified as CST
import Syntax.RST.Terms qualified as RST
import Utils ( Loc, defaultLoc )

---------------------------------------------------------------------------------
-- Resolved Pattern
-- 
-- These are supposed to end up in src/Syntax/RST/Terms.hs eventually, but they
-- are used as an intermediate step here.
---------------------------------------------------------------------------------

data Pattern where
  PatXtor     :: Loc -> PrdCns -> XtorName -> [Pattern] -> Pattern
  PatVar      :: Loc -> PrdCns -> FreeVarName -> Pattern
  PatStar     :: Loc -> PrdCns -> Pattern
  PatWildcard :: Loc -> PrdCns -> Pattern

---------------------------------------------------------------------------------
-- Resolve Pattern
---------------------------------------------------------------------------------

-- | Annotate every part of the pattern with information on whether it stands for
-- a producer or consumer.
resolvePattern :: PrdCns -> CST.Pattern -> ResolverM Pattern
resolvePattern pc (CST.PatXtor loc xt pats) = do
  undefined
resolvePattern Prd (CST.PatVar loc var@(MkFreeVarName name)) = do
  when ("k" `T.isPrefixOf` name) $
    tell [Warning loc ("Producer variable " <> name <> " should not start with letter k")]
  pure $ PatVar loc Prd var
resolvePattern Cns (CST.PatVar loc var@(MkFreeVarName name))  = do
  unless ("k" `T.isPrefixOf` name) $
    tell [Warning loc ("Consumer variable " <> name <> " should start with letter k")]
  pure $ PatVar loc Cns var
resolvePattern pc (CST.PatStar loc) = do
  pure $ PatStar loc pc
resolvePattern pc (CST.PatWildcard loc) = do
  pure $ PatWildcard loc pc

---------------------------------------------------------------------------------
-- Analyze Patterns
---------------------------------------------------------------------------------

data AnalyzedPattern
  = ExplicitPattern Loc XtorName [(PrdCns, FreeVarName)]
  | ImplicitPrdPattern Loc XtorName ([(PrdCns, FreeVarName)], PrdCnsRep Prd,[(PrdCns,FreeVarName)])
  | ImplicitCnsPattern Loc XtorName ([(PrdCns, FreeVarName)], PrdCnsRep Cns,[(PrdCns,FreeVarName)])

isStar :: CST.Pattern -> Bool
isStar (CST.PatStar _) = True
isStar _ = False

fromVar :: CST.Pattern -> FreeVarName
fromVar (CST.PatVar _ var) = var
fromVar _ = error "Called function fromVar on incorrect pattern"

analyzePattern :: DataCodata -> CST.Pattern -> ResolverM AnalyzedPattern
analyzePattern dc (CST.PatXtor loc xt args) = do
  -- Lookup up the arity information in the symbol table.
  (_,res) <- lookupXtor loc xt
  case res of
    (MethodNameResult _cn _arity) -> throwOtherError loc ["Expected xtor but found method " <> unXtorName xt]
    (XtorNameResult dc' _ns arity) -> do
      -- Check whether the Xtor is a Constructor/Destructor as expected.
      case (dc,dc') of
        (Codata,Data  ) -> throwOtherError loc ["Expected a destructor but found a constructor"]
        (Data  ,Codata) -> throwOtherError loc ["Expected a constructor but found a destructor"]
        (Data  ,Data  ) -> pure ()
        (Codata,Codata) -> pure ()
      -- Analyze the pattern
      -- Check whether the number of arguments in the given binding site
      -- corresponds to the number of arguments specified for the constructor/destructor.
      when (length arity /= length args) $
              throwError (LowerError loc (XtorArityMismatch xt (length arity) (length args)) :| [])
      let zipped :: [(PrdCns, CST.Pattern)] = zip arity args
      mapM_ (checkVarName loc) zipped
      case length (filter isStar args) of
        0 -> pure $ ExplicitPattern loc xt $ zip arity (fromVar <$> args)
        1 -> do
          let (args1,(pc,_):args2) = break (\(_,x) -> isStar x) zipped
          case pc of
            Cns -> pure $ ImplicitPrdPattern loc xt (second fromVar <$> args1, PrdRep, second fromVar <$> args2)
            Prd -> pure $ ImplicitCnsPattern loc xt (second fromVar <$> args1, CnsRep, second fromVar <$> args2)
        n -> throwError $ LowerError loc (InvalidStar ("More than one star used in binding site: " <> T.pack (show n) <> " stars used.")) :| []
analyzePattern _ _ =
  throwOtherError defaultLoc ["Reached inaccesible pattern in function analyzePattern"]

analyzeInstancePattern :: CST.Pattern -> ResolverM AnalyzedPattern
analyzeInstancePattern (CST.PatXtor loc xt args) = do
  -- Lookup up the arity information in the symbol table.
  (_,res) <- lookupXtor loc xt
  case res of
    (MethodNameResult _cn arity) -> do
      when (length arity /= length args) $
           throwError $ LowerError loc (XtorArityMismatch xt (length arity) (length args)) :| []
      pure $ ExplicitPattern loc xt $ zip arity (fromVar <$> args)
    (XtorNameResult _dc _ns _arity) -> throwOtherError loc ["Expected method but found Xtor " <> unXtorName xt]
        -- Analyze the pattern
  -- Check whether the number of arguments in the given binding site
  -- corresponds to the number of arguments specified for the constructor/destructor.
analyzeInstancePattern _ =
  throwOtherError defaultLoc ["Error in function analyzeInstancePattern"]

-- | Emit a warning if a producer variable starts with the letter `k`, or a consumer variable doesn't start with the letter `k`.
checkVarName :: Loc -> (PrdCns, CST.Pattern) -> ResolverM ()
checkVarName loc (Prd, CST.PatVar _ (MkFreeVarName name)) = 
  when ("k" `T.isPrefixOf` name) $
    tell [Warning loc ("Producer variable " <> name <> " should not start with letter k")]
checkVarName loc (Cns, CST.PatVar _ (MkFreeVarName name)) = 
  unless ("k" `T.isPrefixOf` name) $
    tell [Warning loc ("Consumer variable " <> name <> " should start with letter k")]
checkVarName _ _ = pure ()