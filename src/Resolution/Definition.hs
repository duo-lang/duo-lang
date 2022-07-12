module Resolution.Definition where

import Control.Monad.Except (MonadError, throwError, ExceptT, runExceptT)
import Control.Monad.Reader
import Data.Bifunctor (second)
import Data.Map (Map)
import Data.Map qualified as M
import Data.List (find)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Text qualified as T

import Pretty.Pretty
import Pretty.Common ()
import Pretty.Types ()
import Resolution.SymbolTable
import Syntax.Common
import Utils
import Errors
import Control.Monad.Writer

------------------------------------------------------------------------------
-- Resolver Monad
------------------------------------------------------------------------------

type ResolveReader = Map ModuleName SymbolTable

type WarningWriter = Writer [Warning]

newtype ResolverM a = MkResolverM { unResolverM :: (ReaderT ResolveReader (ExceptT (NonEmpty Error) WarningWriter)) a }
  deriving (Functor, Applicative, Monad, MonadError (NonEmpty Error), MonadReader ResolveReader, MonadWriter [Warning])

instance MonadFail ResolverM where
  fail str = throwOtherError defaultLoc [T.pack str]

runResolverM :: ResolveReader -> ResolverM a -> (Either (NonEmpty Error) a,[Warning])
runResolverM reader action = runWriter $ runExceptT (runReaderT  (unResolverM action) reader)

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
  symbolTables <- asks M.toList
  let results :: [(ModuleName, Maybe XtorNameResolve)]
      results = second (M.lookup xtor . xtorNameMap) <$> symbolTables
  case filterJusts results of
    []    -> throwOtherError loc ["Constructor/Destructor not in symbol table: " <> ppPrint xtor]
    [res] -> pure res
    _     -> throwOtherError loc ["Constructor/Destructor found in multiple modules: " <> ppPrint xtor]


-- | Find the Arity of a given typename
lookupTypeConstructor :: Loc
                      -- ^ The location of the typename to be looked up
                      -> TypeName
                      -- ^ The typename to look up
                      -> ResolverM TypeNameResolve
                      -- ^ The resolved typename, and the relevant info.
lookupTypeConstructor loc tn = do
    symbolTables <- asks M.toList
    let results :: [(ModuleName, Maybe TypeNameResolve)]
        results = second (M.lookup tn . typeNameMap) <$> symbolTables
    case filterJusts results of
      []         -> throwOtherError loc ["Type name " <> unTypeName tn <> " not found in symbol table."]
      [(_,res)]  -> pure res
      xs         -> throwOtherError loc ["Type name " <> unTypeName tn <> " found in multiple imports.\nModules: " <> T.pack (show(fst <$> xs))]

-- | Type operator for the union type
unionTyOp :: TyOp
unionTyOp = MkTyOp
  { symbol = UnionOp
  , prec = MkPrecedence 1
  , assoc = LeftAssoc
  , desugar = UnionDesugaring
  }

-- | Type operator for the intersection type
interTyOp :: TyOp
interTyOp = MkTyOp
  { symbol = InterOp
  , prec = MkPrecedence 2
  , assoc = LeftAssoc
  , desugar = InterDesugaring
  }

lookupTyOp :: Loc
           -> BinOp
           -> ResolverM (ModuleName, TyOp)
lookupTyOp _ UnionOp = pure (MkModuleName "<BUILTIN>", unionTyOp)
lookupTyOp _ InterOp = pure (MkModuleName "<BUILTIN>", interTyOp)
lookupTyOp loc op = do
  symbolTables <- asks M.toList
  let results :: [(ModuleName, Maybe TyOp)]
      results = second (find (\tyop -> symbol tyop == op) . tyOps) <$> symbolTables
  case filterJusts results of
    []    -> throwError (LowerError loc (UnknownOperator (ppPrint op)) NE.:| [])
    [res] -> pure res
    _     -> throwOtherError loc ["Type operator " <> ppPrint op <> " found in multiple imports."]
      