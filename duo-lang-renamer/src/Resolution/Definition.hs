module Resolution.Definition where

import Control.Monad.Except (MonadError, throwError, ExceptT, runExceptT)
import Control.Monad.Reader
import Data.Bifunctor (second)
import Data.Map (Map)
import Data.Map qualified as M
import Data.Text qualified as T

import Resolution.SymbolTable
import Syntax.CST.Names
import Syntax.RST.Names
import Syntax.CST.Kinds (PolyKind)
import Loc
import Errors.Renamer
import Control.Monad.Writer
import qualified Data.Set as S

------------------------------------------------------------------------------
-- Resolver Monad
------------------------------------------------------------------------------

data ResolveReader = ResolveReader { rr_modules :: Map ModuleName SymbolTable, rr_recVars :: S.Set RecTVar , rr_ref_recVars :: Map RecTVar (TypeName, PolyKind)}

type WarningWriter = Writer [Warning]

newtype ResolverM a = MkResolverM { unResolverM :: (ReaderT ResolveReader (ExceptT ResolutionError WarningWriter)) a }
  deriving newtype (Functor, Applicative, Monad, MonadError ResolutionError, MonadReader ResolveReader, MonadWriter [Warning])

instance MonadFail ResolverM where
  fail str = throwError (UnknownResolutionError defaultLoc (T.pack str))

runResolverM :: ResolveReader -> ResolverM a -> (Either ResolutionError a,[Warning])
runResolverM reader action = runWriter $ runExceptT (runReaderT  action.unResolverM reader)

------------------------------------------------------------------------------
-- Helper Functions
------------------------------------------------------------------------------

filterJusts :: [(a, Maybe b)] -> [(a,b)]
filterJusts [] = []
filterJusts ((_,Nothing):xs) = filterJusts xs
filterJusts ((x,Just y):xs) = (x,y):filterJusts xs

lookupXtor :: Loc
           -- ^ The location of the xtor to be looked up
           -> XtorName
           -- ^ The name of the xtor and whether we expect a ctor or dtor
           -> ResolverM (ModuleName, XtorNameResolve)
           -- ^ The module where the xtor comes from, its sort and arity.
lookupXtor loc xtor = do
  symbolTables <- asks (M.toList . (\x -> x.rr_modules))
  let results :: [(ModuleName, Maybe XtorNameResolve)]
      results = second (M.lookup xtor . (\x -> x.xtorNameMap)) <$> symbolTables
  case filterJusts results of
    []    -> throwError (XtorNotFound loc xtor)
    [res] -> pure res
    _     -> throwError (XtorAmbiguous loc xtor)


-- | Find the Arity of a given typename
lookupTypeConstructor :: Loc
                      -- ^ The location of the typename to be looked up
                      -> TypeName
                      -- ^ The typename to look up
                      -> ResolverM TypeNameResolve
                      -- ^ The resolved typename, and the relevant info.
lookupTypeConstructor loc tn = do
    symbolTables <- asks (M.toList . (\x -> x.rr_modules))
    let results :: [(ModuleName, Maybe TypeNameResolve)]
        results = second (M.lookup tn . (\x -> x.typeNameMap)) <$> symbolTables
    case filterJusts results of
      []         -> throwError (TypeNameNotFound loc tn)
      [(_,res)]  -> pure res
      _          -> throwError (TypeNameAmbiguous loc tn)

-- | Type operator for the union type
unionTyOp :: BinOpDescr
unionTyOp = MkBinOpDescr
  { prec = MkPrecedence 1
  , assoc = LeftAssoc
  , desugar = UnionDesugaring
  }

-- | Type operator for the intersection type
interTyOp :: BinOpDescr
interTyOp = MkBinOpDescr
  { prec = MkPrecedence 2
  , assoc = LeftAssoc
  , desugar = InterDesugaring
  }

lookupTyOp :: Loc
           -> BinOp
           -> ResolverM (ModuleName, BinOpDescr)
lookupTyOp _ UnionOp = pure (MkModuleName [] "<BUILTIN>", unionTyOp)
lookupTyOp _ InterOp = pure (MkModuleName [] "<BUILTIN>", interTyOp)
lookupTyOp loc (CustomOp sym) = do
  symbolTables <- asks $ M.toList . (\x -> x.rr_modules)
  let results :: [(ModuleName, Maybe BinOpDescr)]
      results = second (M.lookup sym . (\x -> x.tyOps)) <$> symbolTables
  case filterJusts results of
    []    -> throwError (TypeOperatorNotFound loc sym)
    [res] -> pure res
    _     -> throwError (TypeOperatorAmbiguous loc sym)

